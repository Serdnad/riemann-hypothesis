module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle005
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle001
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Decay

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_sizeInf {d : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

theorem continuous_sizeTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup (M := M) (n := n) b) := by
  unfold sizeTup
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
  exact (continuous_sizeInf b).comp ((continuous_apply i).comp (continuous_apply a))

theorem rapidDecay_of_compact {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    RapidDecay b Φ := by
  intro N
  have hcont : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    (continuous_norm.comp hc).mul ((continuous_const.add (continuous_sizeTup b)).pow N)
  have hsupp : HasCompactSupport fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    hs.norm.mul_right
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨C, fun X => le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC X)⟩

end Decay

theorem sWeqOm_of (h1 : DensFibInf) (h2 : DensFibV) : SWeqOm := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν Φ hΦ
  obtain ⟨d, b, Φinf, Φf, Φv, hci, hsi, hpf, hpr, hsm⟩ := hΦ
  have hS := hc a ha2 (gramE σ J X0) hT hdet d b Φ Φinf Φf Φv hci
    (rapidDecay_of_compact b Φinf hci hsi) hsm hpf hpr
  obtain ⟨_, hν2⟩ := hν
  obtain ⟨μinf, hμinf⟩ := hν2.1
  have hν3 := hν2.2 μinf hμinf
  obtain ⟨νinf, hνinf⟩ := hν3.1
  have hν4 := hν3.2 νinf hνinf
  obtain ⟨μv, hμv⟩ := hν4.1
  have hν5 := hν4.2 μv hμv
  obtain ⟨νv, hνv⟩ := hν5.1
  have hν6 := hν5.2 νv hνv
  obtain ⟨fibInf, hfibInf⟩ := hν6.1
  have hν7 := hν6.2 fibInf hfibInf
  obtain ⟨fibV, hfibV⟩ := hν7.1
  have hν8 := hν7.2 fibV hfibV d b Φ Φinf Φf Φv hci hsi hpf hpr
  obtain ⟨ginf, gv, hdi, hdv, _, hmean⟩ :=
    (((((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv)
  have hmean' : meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = gramE σ J X0}) =
      ginf (hermOf (Ainf F) σ (gramE σ J X0) hT) *
        ∏' v, gv v (hermOf (Fv F v) σ (gramE σ J X0) hT) := hmean
  rw [hmean', hν8.2.2, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
    fibInf hfibInf Φinf ginf hci hsi hdi]
  congr 1
  exact tprod_congr fun v => h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfibV v) (Φv v) (gv v) (hpf.1 v) (hdv v)

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

@[reducible] def starOfInv {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) :
    StarRing E where
  star := σ
  star_involutive := hσ
  star_mul x y := by
    show σ (x * y) = σ y * σ x
    rw [map_mul, mul_comm]
  star_add x y := map_add σ x y

section General

variable {E : Type} [Field E] {M : ℕ}

theorem hform_add_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J (c • x) y = σ c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J x (c • y) = RingHom.id E c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable [StarRing E]

def hSes (J : Matrix (Fin M) (Fin M) E) : (Fin M → E) →ₗ⋆[E] (Fin M → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (hform_add_left' _ J) (hform_smul_left' _ J) (hform_add_right' _ J) (hform_smul_right' _ J)

theorem hSes_apply (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hSes J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hSes_herm (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (x y : Fin M → E) : star (hSes J x y) = hSes J y x := by
  rw [hSes_apply, hSes_apply]
  show starRingEnd E _ = _

  simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem hSes_nondeg (J : Matrix (Fin M) (Fin M) E) (hdet : J.det ≠ 0) (x : Fin M → E)
    (hx : ∀ y, hSes J x y = 0) : x = 0 := by
  have h1 : (fun i => starRingEnd E (x i)) ᵥ* J = 0 := by
    funext j
    have := hx (Pi.single j 1)
    rw [hSes_apply] at this
    simpa [Formalism.UG.hform, Pi.single_apply, vecMul, dotProduct] using this
  have h2 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  funext i
  have := congrFun h2 i
  simpa using this

theorem linInd_of_gram (J : Matrix (Fin M) (Fin M) E) {a : ℕ} (X : Fin a → Fin M → E)
    (G : Matrix (Fin a) (Fin a) E) (hG : ∀ i j, G i j = Formalism.UG.hform (starRingEnd E) J (X i) (X j))
    (hdet : G.det ≠ 0) : LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : G *ᵥ c = 0 := by
    funext j
    have := congrArg (hSes J (X j)) hc

    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [mulVec, dotProduct, Pi.zero_apply, hG]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSes_apply]
    ring
  intro i
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h1) i

variable [CharZero E]

theorem witt_tuple (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (hdet : J.det ≠ 0) {a : ℕ} (X0 X : Fin a → Fin M → E) (h0 : LinearIndependent E X0)
    (h1 : LinearIndependent E X)
    (hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j)) :
    ∃ g ∈ Formalism.UG.UJ (starRingEnd E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E) *ᵥ X0 i = X i := by
  let U := Submodule.span E (Set.range X0)
  let bU : Module.Basis (Fin a) E U := Module.Basis.span h0
  have hb : ∀ i, ((bU i : U) : Fin M → E) = X0 i := fun i => by
    show ((Module.Basis.span h0 i : U) : Fin M → E) = X0 i
    rw [Module.Basis.span_apply]
  let f : U →ₗ[E] (Fin M → E) := bU.constr E X
  have hf : ∀ i, f (bU i) = X i := fun i => bU.constr_basis E X i
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hs := bU.sum_repr u
    rw [← hs] at hu

    simp only [map_sum, map_smul, hf] at hu
    have hc := (Fintype.linearIndependent_iff.mp h1) _ hu
    rw [← hs]
    simp [hc]
  have key : ((hSes J).comp f).compl₂ f = ((hSes J).comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis bU bU fun i j => ?_
    show hSes J (f (bU i)) (f (bU j)) = hSes J ((bU i : U) : Fin M → E) ((bU j : U) : Fin M → E)
    rw [hf, hf, hb, hb]
    exact hG i j
  have hiso : ∀ x y : U, hSes J (f x) (f y) = hSes J x y := fun x y =>
    DFunLike.congr_fun (DFunLike.congr_fun key x) y
  obtain ⟨g, hgiso, hgf⟩ :=
    witt_extension_theorem E (Fin M → E) (hSes J) (hSes_herm J hJ) (hSes_nondeg J hdet) U f hinj hiso
  let m : Matrix (Fin M) (Fin M) E := LinearMap.toMatrix' (g : (Fin M → E) →ₗ[E] (Fin M → E))
  let mi : Matrix (Fin M) (Fin M) E :=
    LinearMap.toMatrix' (g.symm : (Fin M → E) →ₗ[E] (Fin M → E))
  have hc1 : (g : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hc2 : (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hm1 : m * mi = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc1, LinearMap.toMatrix'_id]
  have hm2 : mi * m = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc2, LinearMap.toMatrix'_id]
  have hmv : ∀ v, m *ᵥ v = g v := fun v => by
    simp only [m]
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  refine ⟨⟨m, mi, hm1, hm2⟩, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd E) m * J * m = J
    ext i j
    have h := hgiso (Pi.single i 1) (Pi.single j 1)
    rw [hSes_apply, hSes_apply, ← hmv, ← hmv, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single,
      Formalism.UG.P.hform_single] at h
    exact h
  · intro i
    show m *ᵥ X0 i = X i
    rw [hmv, ← hb i]
    exact (hgf (bU i)).trans (hf i)

end General

theorem sigma_invol_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem witt_holds : Witt := by
  unfold Witt InCtx
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 _ hdet X hX
  letI : StarRing E := starOfInv (σ : E →+* E) (sigma_invol_cm σ hCM)
  have hs : starRingEnd E = (σ : E →+* E) := RingHom.ext fun _ => rfl
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := by
    rw [hs]; exact hJ.1
  have hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j) := by
    rw [hs]; exact fun i j => congrFun (congrFun hX i) j
  have hl0 : LinearIndependent E X0 :=
    linInd_of_gram J X0 (gramE σ J X0) (by rw [hs]; intro i j; rfl) hdet
  have hl1 : LinearIndependent E X :=
    linInd_of_gram J X (gramE σ J X) (by rw [hs]; intro i j; rfl) (hX ▸ hdet)
  obtain ⟨g, hg, hgX⟩ := witt_tuple J hJ' hJ.2 X0 X hl0 hl1 hG
  rw [hs] at hg
  exact ⟨g, hg, hgX⟩

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem countable_numberField : Countable F :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

theorem separableSpace_Fv : TopologicalSpace.SeparableSpace (Fv F v) := by
  haveI := countable_numberField F
  exact ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
    HeightOneSpectrum.denseRange_algebraMap F v⟩⟩

theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  haveI := separableSpace_Fv F v
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) := by
  have hK := PI.AdicCompletionValuation.isCompact_adicCompletionIntegers (F := F) (v := v)
  have hN : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∈ 𝓝 (0 : v.adicCompletion F) := by
    exact (Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers F).zero_mem
  exact hK.locallyCompactSpace_of_mem_nhds_of_addGroup hN

theorem isOpen_units_Fv : IsOpen {r : Fv F v | IsUnit r} := by
  have h : {r : Fv F v | IsUnit r} = {0}ᶜ := by
    ext r
    simp [isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton

end Local

theorem densFibV_holds : DensFibV := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ v μv hμv νv hνv fibV hfib Φv gv
    hSB hdens
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  exact DensGen.densGen (B := Set.univ) hfib (continuous_gramH (Fv F v) σ hσ J hJ.1)
    (fun X => rfl) Subtype.val_injective
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX)
    hSB.1.continuous hSB.2 hdens Filter.univ_mem
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def SCHA : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def DiscHF : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  DiscreteTopology (HFinIn (AF F) σ J)

theorem exFDStab_of (h1 : SCHA) (h2 : DiscHF) : ExFDStab := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' _hμ'
  have i1 : SecondCountableTopology (HA (AF F) σ J) := h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i2 : DiscreteTopology (HFinIn (AF F) σ J) := h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i3 : SecondCountableTopology (stabT (AF F) σ J X0) :=
    TopologicalSpace.Subtype.secondCountableTopology (stabT (AF F) σ J X0 : Set (HA (AF F) σ J))
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_subtype_val :
      Continuous fun x : ratIn F E σ M J (stabT (AF F) σ J X0) => ((x : stabT (AF F) σ J X0) : HA (AF F) σ J))).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : DiscreteTopology (ratIn F E σ M J (stabT (AF F) σ J X0)) := DiscreteTopology.of_continuous_injective hf hinj
  obtain ⟨𝓕, -, h𝓕⟩ := PI.VolSemiDirect.W.exists_fd (G := stabT (AF F) σ J X0) (ratIn F E σ M J (stabT (AF F) σ J X0))
  exact ⟨𝓕, h𝓕 μ'⟩

theorem discHF_of_discHA (h : PI.VolSemiDirect.W.DiscHA) : DiscHF := by
  intro F E _ _ _ _ _ σ hE M J hJ _ _ _ _ _ _ _ _
  exact (h F E σ hE M J hJ).2

end PI.VolStabS
end
end
