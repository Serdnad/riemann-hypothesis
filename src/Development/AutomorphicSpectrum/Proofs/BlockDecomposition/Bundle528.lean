module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import GroundTheory.AutomorphicForms.Bundle012
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.MirSides

open Matrix PositivityTheory.RgEis PositivityTheory.RgEis.MG
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
open GlobalTheory.CompanionTheory.CMMirror
open scoped NumberField.AdeleRing
open NumberField

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tInv_dgl (d : ι → IdeleGroup k) : tInv (dgl d) = dgl fun i => (d i)⁻¹ := by
  ext r c
  rw [tInv_coe]
  show (Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]))ᵀ r c =
    Matrix.diagonal (fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])) r c
  rw [Matrix.diagonal_transpose]

theorem tInv_mem_ratGL {E R : Type} [Field E] [CommRing R] (A : Ad E R) (g : GL ι R) (h : g ∈ A.ratGL ι) :
    tInv g ∈ A.ratGL ι := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨tInv x, (tInv_map _ x).symm⟩

variable {G : Type} [Group G]

theorem kap_tInv (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (g : G) :
    kap (tInv.comp π) (fun i => (d i)⁻¹) g = tInv (kap π d g) := by
  unfold kap
  rw [MonoidHom.comp_apply, ← tInv_dgl, map_mul, map_mul, map_inv]

theorem kap_mem [TopologicalSpace G] {π : G →* GL ι 𝔸[k]} {Γ K : Subgroup G} {i₀ i₁ : ι} {ω : HeckeCharacter k}
    {d : ι → IdeleGroup k} {c : G → ℂ} {η η' l : G → ℝ} (h : MirData π Γ K i₀ i₁ ω d c η η' l) (κ : G) (hκ : κ ∈ K) :
    kap π d κ ∈ (adStd k).kGL ι := by
  obtain ⟨κ', hκ', e⟩ := h.piK κ hκ
  have e' : π κ * dgl d = dgl d * κ' := Units.ext e
  have : kap π d κ = κ' := by
    unfold kap
    rw [mul_assoc, e', inv_mul_cancel_left]
  rw [this]
  exact hκ'

theorem bdet_tInv_of_mem {R : Type} [CommRing R] {i : ι}
    (hmul : ∀ p ∈ stab R ({i} : Set ι), ∀ q ∈ stab R ({i} : Set ι),
      bdet ({i} : Set ι) (p * q) = bdet {i} p * bdet {i} q)
    (p : GL ι R) (hp : p ∈ stab R ({i}ᶜ : Set ι)) : bdet ({i} : Set ι) (tInv p) = (bdet {i} p)⁻¹ := by
  have h1 : tInv p ∈ stab R ({i} : Set ι) := (tInv_mem_stab p {i}).2 hp
  have h2 : tInv p⁻¹ ∈ stab R ({i} : Set ι) := (tInv_mem_stab p⁻¹ {i}).2 (inv_mem hp)
  have e := hmul _ h1 _ h2
  have b1 : bdet ({i} : Set ι) (1 : GL ι R) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_mul.1 this
  rw [← map_mul, mul_inv_cancel, map_one, b1, bdet_tInv {i} p⁻¹, inv_inv] at e
  exact eq_inv_of_mul_eq_one_left e.symm

theorem lg_inv {A : Ad k 𝔸[k]} (h : A.GoodL) (b : (𝔸[k])ˣ) : A.lg b⁻¹ = - A.lg b := by
  have h1 := h.lgmul 1 1
  have h2 := h.lgmul b b⁻¹
  rw [mul_one] at h1
  rw [mul_inv_cancel] at h2
  linarith

theorem toIdele_inv {ω : HeckeCharacter k} (h : ω * ω = 1) (b : IdeleGroup k) :
    ω.toIdele b⁻¹ = ω.toIdele b := by
  have e : ω.toIdele b * ω.toIdele b = 1 := by
    rw [HeckeCharacter.toIdele_apply]
    exact DFunLike.congr_fun h (IdeleClassGroup.mk k b)
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_right e

theorem modPow_one_eq (x : IdeleGroup k) :
    modPow x 1 = Complex.exp ((adStd k).lg x : ℝ) := by
  have hp : 0 < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  show _ = Complex.exp ((Real.log (IdeleGroup.ideleModule k x : ℝ) : ℝ) : ℂ)
  rw [← Complex.ofReal_exp, Real.exp_log hp, modPow, Complex.cpow_one]

theorem sideOf : StdGood → BdetLaw → SideOf := by
  intro hS hB G _ _ _ _ K _ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l h
  have hG := hS k
  have hmul := (hB k 𝔸[k] (adStd k) hG ι {i₁}).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { two := h.two
        sq := h.sq
        cont := h.cont
        piK := kap_mem h
        piΓ := h.piΓ
        trans := h.trans _ (Or.inl rfl)
        mem := fun _ => Iff.rfl
        par := h.par
        ht := h.ht
        val := fun p hp => h.val p hp }
  · refine
      { two := h.two
        sq := h.sq
        cont := cont_tInv.comp h.cont
        piK := fun κ hκ => ?_
        piΓ := fun γ hγ => tInv_mem_ratGL _ _ (h.piΓ γ hγ)
        trans := fun g hg => ?_
        mem := fun g => (tInv_mem_stab (π g) {i₁}).symm
        par := h.par'
        ht := h.ht'
        val := fun p hp => ?_ }
    · rw [kap_tInv]
      exact tInv_mem_kGL _ _ (kap_mem h κ hκ)
    · obtain ⟨γ, hγ, e⟩ := h.trans {i₁}ᶜ (Or.inr rfl) (tInv g) (tInv_mem_ratGL _ _ hg)
      refine ⟨γ, hγ, ?_⟩
      have e' := (tInv_mem_stab _ {i₁}).2 e
      rw [map_mul, tInv_tInv, map_inv] at e'
      exact e'
    · have hp' : π p ∈ stab 𝔸[k] ({i₁}ᶜ : Set ι) := hp
      have hb := bdet_tInv_of_mem hmul (π p) hp'
      obtain ⟨v1, v2⟩ := h.val' p hp'
      refine ⟨?_, ?_⟩
      · show c p = ω.toIdele (bdet {i₁} (tInv (π p)))
        rw [hb, toIdele_inv h.sq]
        exact v1
      · show η' p = (adStd k).lg (bdet {i₁} (tInv (π p)))
        rw [hb, lg_inv hG]
        exact v2
  · intro g
    rw [map_mul, tInv_dgl]
    rfl
  · intro g
    rw [map_mul, modPow_mul, modPow_one_eq (Matrix.GeneralLinearGroup.det (π g)), ← h.vall g]

end GlobalTheory.CompanionTheory.MirSides
end
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.So

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisFix

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  obtain ⟨-, hC, -, hτ⟩ := h
  by_contra hno
  push Not at hno
  let τ : E →+* ℂ := Classical.arbitrary _
  have hR : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact ((hτ τ x).symm.trans (congrArg τ (hno x)) : _)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (hC.isComplex (InfinitePlace.mk τ)))
    (InfinitePlace.isReal_mk_iff.2 hR)

theorem add_conj_mem (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) :
    ∃ c : F, e + σ e = algebraMap F E c := by
  let S : Submodule F E := LinearMap.eqLocus σ.toLinearMap LinearMap.id
  have hS : S ≠ ⊤ := by
    obtain ⟨y, hy⟩ := exists_moved σ h
    intro hT
    have hyS : y ∈ S := hT ▸ Submodule.mem_top
    exact hy hyS
  have h1 : Submodule.span F {(1 : E)} ≤ S := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact map_one σ
  have hlt : Module.finrank F S < 2 := h.2.2.1 ▸ Submodule.finrank_lt hS
  have hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1 :=
    finrank_span_singleton one_ne_zero
  have heq : Submodule.span F {(1 : E)} = S :=
    Submodule.eq_of_le_of_finrank_le h1 (by omega)
  have hmem : e + σ e ∈ S := by
    change σ (e + σ e) = e + σ e
    rw [map_add (f := _), conj_conj σ h, add_comm]
  rw [← heq, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩

def halfTr (σ : E →ₐ[F] E) : E →ₗ[F] F :=
  (4⁻¹ : F) • (Algebra.trace F E ∘ₗ (LinearMap.id + σ.toLinearMap))

theorem algebraMap_halfTr (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (halfTr σ e) = (2⁻¹ : F) • (e + σ e) := by
  obtain ⟨c, hc⟩ := add_conj_mem σ h e
  have hval : halfTr σ e = 2⁻¹ * c := by
    simp only [halfTr, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, smul_eq_mul]
    rw [hc, Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul]
    push_cast
    ring
  rw [hval, hc, Algebra.smul_def, map_mul]

theorem halfTr_one (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : halfTr σ (1 : E) = 1 := by
  apply (algebraMap F E).injective
  rw [algebraMap_halfTr σ h, map_one, map_one, Algebra.smul_def, map_inv₀, map_ofNat]
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  field_simp
  norm_num

def rr (σ : E →ₐ[F] E) : AE F E →ₗ[AF F] AF F :=
  (TensorProduct.AlgebraTensorModule.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor (AF F) (AF F) (halfTr σ)

theorem rr_tmul (σ : E →ₐ[F] E) (a : AF F) (e : E) : rr σ (a ⊗ₜ[F] e) = halfTr σ e • a := by
  simp [rr]

theorem nu_apply (x : AF F) : nuCM F E x = x ⊗ₜ[F] (1 : E) := rfl

theorem rr_nu (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : AF F) : rr σ (nuCM F E x) = x := by
  rw [nu_apply, rr_tmul, halfTr_one σ h, one_smul]

theorem cA_nu (σ : E →ₐ[F] E) (x : AF F) : cA σ (nuCM F E x) = nuCM F E x := by
  simp [nu_apply, cA]

theorem nu_rr (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AE F E) :
    nuCM F E (rr σ z) = (2⁻¹ : F) • (z + cA σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), ← smul_add]
    congr 1
    abel
  | tmul a e =>
    have hc : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [rr_tmul, nu_apply, hc, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul,
      ← algebraMap_halfTr σ h, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']

theorem continuous_nu : Continuous (nuCM F E) := by
  have h : (nuCM F E : AF F → AE F E) = fun x => x • (1 : AE F E) := by
    funext x
    rw [nu_apply, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact Continuous.smul (f := fun x : AF F => x) (g := fun _ => (1 : AE F E)) continuous_id continuous_const

theorem bFix : BFix := by
  intro F E _ _ _ _ _ σ χ c hCM _ _ _
  refine ⟨continuous_nu, Function.LeftInverse.injective (rr_nu σ hCM), cA_nu σ, rr σ,
    IsModuleTopology.continuous_of_linearMap (rr σ), fun x hx => ?_⟩
  have hx' : cA σ x = x := hx
  rw [nu_rr σ hCM, hx', ← two_smul F x, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

end GlobalTheory.CompanionTheory.RgEisFix
end
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisBrat

open scoped TensorProduct NumberField.AdeleRing
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

theorem brat : BRat := by
  intro F E _ _ _ _ _ σ χ c _ _ _ _
  refine ⟨fun y => ?_, fun e x h => ?_⟩
  · change (algebraMap F (AF F) y) ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] (algebraMap F E y)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · obtain ⟨g, hg⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F E))
    have g1 : g 1 = 1 := by
      have := LinearMap.congr_fun hg (1 : F)
      simpa using this
    have h' : (1 : AF F) ⊗ₜ[F] e = x ⊗ₜ[F] (1 : E) := h
    have h2 := congrArg (fun t => TensorProduct.rid F (AF F) (LinearMap.lTensor (AF F) g t)) h'
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at h2
    refine ⟨g e, ?_⟩
    rw [← h2, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CompanionTheory.EisBrat
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField Matrix
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisSo

theorem jtop : JTop := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν _ δ _ _ ι _ _ _ j hA hB _ hJ
  have hcv : Continuous ν := hB.cont

  have hval : Continuous fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    have e : (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = fun x =>
        (x.1.1 : R) • ((((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) *
          ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν) *
          ((dg ι (Units.map A.i.toMonoidHom δ) : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) := by
      funext x; rw [hJ x]; rfl
    rw [e]
    have h1 : Continuous fun x : cover A ν ι => (x.1.1 : R) :=
      Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : cover A ν ι => (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) :=
      Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    exact h1.smul ((continuous_const.matrix_mul (h2.matrix_map hcv)).matrix_mul continuous_const)
  have hjGL : Continuous fun x : cover A ν ι => ((j x).1 : GL (ι ⊕ ι) R) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have e : (fun x : cover A ν ι => (((((j x).1 : GL (ι ⊕ ι) R))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) =
        (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) ∘ fun x => x⁻¹ := by
      funext x; simp [map_inv]
    rw [e]; exact hval.comp continuous_inv
  have hum : ∀ {S T : Type} [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T]
      [IsTopologicalRing S] (φ : S →+* T), Continuous φ → Continuous (Units.map φ.toMonoidHom) := by
    intro S T _ _ _ _ _ φ hφ
    exact Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val, hφ.comp (Units.continuous_val.comp continuous_inv)⟩
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩
  haveI : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) := inferInstanceAs (SecondCountableTopology (ι ⊕ ι → ι ⊕ ι → 𝔸[F]))
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology Rˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace Rˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (ι ⊕ ι) 𝔸[F]) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have hf : Continuous fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
      x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2) :=
    (continuous_fst.mul ((hum A.σ hA.σcont).comp continuous_fst)).mul ((hum ν hcv).comp (hdet.comp continuous_snd))
  have hcl : IsClosed (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) := by
    have e : (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) = (fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
        x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)) ⁻¹' {1} :=
      Set.ext fun x => Iff.rfl
    rw [e]; exact isClosed_singleton.preimage hf
  haveI : SecondCountableTopology (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance
  exact ⟨hjGL.subtype_mk _, inferInstance, hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩

end GlobalTheory.CompanionTheory.EisSo
end

section

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisSo

theorem jCh : StdGood → BdetLaw → JTop → JCh := by
  intro hS hB _ F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hBase hi hJ
  have hL : (adStd F).GoodL := hS F
  obtain ⟨-, -, -, -, hk, hd⟩ := hB F 𝔸[F] (adStd F) hL (ι ⊕ ι) Set.univ
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) := by
    have h := Continuous.units_map (Matrix.detMonoidHom (n := ι ⊕ ι) (R := 𝔸[F]))
      (Continuous.matrix_det continuous_id)
    convert h using 1
    funext x
    apply Units.ext
    rfl
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hfst : Continuous fun x : cover A ν ι => x.1.1 := continuous_fst.comp continuous_subtype_val
  have hadd : ∀ p g : cover A ν ι, ld (p * g) = ld p + ld g := by
    intro p g
    simp only [ld, map_mul]
    exact hL.lgmul _ _
  have hK : ∀ k ∈ cK α j, ld k = 0 := by
    intro k hk'
    obtain ⟨κ, hκ, he⟩ := hk'.2
    have hdk : Matrix.GeneralLinearGroup.det (prj A ν ι k) = Matrix.GeneralLinearGroup.det κ := by
      rw [← he]
      simp [MulAut.conj_apply, map_mul, map_inv, mul_comm]
    have := hk κ (by intro r hr; exact absurd (Set.mem_univ r) hr) hκ
    rw [hd] at this
    simp only [ld, hdk]
    exact this
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p _ q _
    simp [c0]
  · intro p _
    exact Circle.norm_coe _
  · intro γ hγ _
    obtain ⟨⟨x, hx⟩, -⟩ := hγ
    have := hG.toGoodL.χi x
    simp only [c0]
    have hx' : Units.map A.i.toMonoidHom x = γ.1.1 := hx
    rw [← hx', this]
    simp
  · exact (continuous_subtype_val.comp (hG.toGoodL.χcont.comp hfst)).continuousOn
  · intro p _ g
    exact hadd p g
  · intro g k hk'
    rw [hadd, hK k hk', add_zero]
  · intro γ hγ _
    obtain ⟨-, ⟨g, hg⟩⟩ := hγ
    have e : Matrix.GeneralLinearGroup.det (prj A ν ι γ) = Units.map (adStd F).i.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
      have hg' : Matrix.GeneralLinearGroup.map (adStd F).i g = γ.1.2 := hg
      show Matrix.GeneralLinearGroup.det γ.1.2 = _
      rw [← hg']
      apply Units.ext
      show ((Matrix.GeneralLinearGroup.map (adStd F).i g : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).det =
        (adStd F).i (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F).det
      rw [RingHom.map_det]
      rfl
    simp only [ld, e]
    exact hL.lgi _
  · exact hL.lgcont.comp (hdet.comp hprj)

end GlobalTheory.CompanionTheory.EisSo
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

def lowC (g : G D p) : Mx D p p :=
  (mat g).submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inl j))

def lowD (g : G D p) : Mx D p p :=
  (mat g).submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inr j))

def InCell (e : AE D) (g : G D p) : Prop := ∃ y : Mx D p p, mm y (lowC g) = e • (1 : Mx D p p)

def IsB (e : AE D) (g : G D p) (x : hermS D p e) : Prop := InCell e g ∧ mm (lowC g) x.1.1 = e • lowD g


end GlobalTheory.CompanionTheory.MuC

end
end
