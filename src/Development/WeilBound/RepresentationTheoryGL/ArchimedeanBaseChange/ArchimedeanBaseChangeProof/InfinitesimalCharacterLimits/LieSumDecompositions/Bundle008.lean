module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle590
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ExpChar
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSliceUA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle006
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle010
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceE
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceF
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem zalg_comm {N : ℕ} {I : Submodule ℂ (Sm E N)} (hI : ∀ X, ∀ φ ∈ I, lie E N X φ ∈ I)
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Zalg E N) : ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    { carrier := {z | ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ)}
      mul_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hy φ hφ
        obtain ⟨h2, e2⟩ := hx _ h1
        exact ⟨h2, by simp only [Module.End.mul_apply]; rw [e2, e1]⟩
      add_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hx φ hφ
        obtain ⟨h2, e2⟩ := hy φ hφ
        exact ⟨add_mem h1 h2, by simp only [LinearMap.add_apply, map_add (f := _), e1, e2]⟩
      algebraMap_mem' := fun c φ hφ => ⟨by simpa only [Module.algebraMap_end_apply] using I.smul_mem c hφ,
        by simp only [Module.algebraMap_end_apply, map_smul]⟩ }
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap τ u ∈ S := fun τ u φ hφ =>
    ⟨Zalg_stable hI (cap_mem_Zalg τ u) φ hφ, GlobalTheory.SpehInfChar.cap_comm_quot hI f hf τ u φ hφ⟩
  have hle : Zalg E N ≤ S := Algebra.adjoin_le (by rintro _ ⟨τ, u, rfl⟩; exact hcap τ u)
  exact hle hz

variable {r s : ℕ}

theorem expand {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) : ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ Submodule.span ℂ (lsF r s (T ψ) k g)) ∧
        (∀ i, q i ∈ rsF r s (T ψ) k g) ∧
        ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  intro ψ hψ k g
  have hAψ : IsAutForm ψ := hU.2 ψ hψ
  have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ

  let L := GlobalTheory.DiscClosure.stabSub ψ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAψ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T ψ) = T ψ := fun h hh => by
    have e := hT.equiv (.fin h) ψ hψ
    have hh' : finRep E (r + s) h ψ = ψ := hh
    change T (finRep E (r + s) h ψ) = finRep E (r + s) h (T ψ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T ψ)
  have : FiniteDimensional ℂ S := by
    have := hAψ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ ψ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hT.equiv (.cpt κ) ψ hψ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T ψ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g' : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T ψ)).1 g') ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g' =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T ψ, Submodule.subset_span ⟨1, by simp⟩⟩ g'

  have := hAψ.zfin
  let J : Set (Module.End ℂ (Sm E (r + s))) := {z | z ∈ Zalg E (r + s) ∧ z ψ = 0}
  have hJ : Cofin J := PositivityTheory.Rg.Rs.JFinTr.cofin_ann ψ
  have hJZ : J ⊆ Zalg E (r + s) := fun z hz => hz.1
  have hZ : ∀ z ∈ J, z (T ψ) = 0 := by
    rintro z ⟨hz, hzψ⟩
    rw [← (zalg_comm hI T hT.equiv hz ψ hψ).2, hzψ, map_zero]
  obtain ⟨J₁, -, c₁, -, k₁, -⟩ := centre J hJ

  let L₁ := Slice1.levelOne s L g
  let ρ₁ := ρ.comp (Slice1.levK E r s)
  have := PositivityTheory.Rg.HF.GL.genFin E r L₁ (Slice1.isOpen_levelOne hLo g) S ρ₁
    (fun ℓ w => (hρ ℓ w).comp Slice1.continuous_levK) J₁ c₁
  let S₁ := Submodule.span ℂ (lsF r s (T ψ) k g) ⊓ Submodule.span ℂ (genSpace L₁ ρ₁ J₁)
  have : FiniteDimensional ℂ S₁ := Submodule.finiteDimensional_of_le inf_le_right
  let U' := S₁.map (Sm E r).subtype
  obtain ⟨P, a, ha⟩ := SliceTensor.interp U'
  let f : GA E r × GA E s → ℂ := fun m => (T ψ).1 (lev (Ad E) r s m * yp k g)
  have hleft : ∀ m₂, (fun m₁ => f (m₁, m₂)) ∈ U' := by
    intro m₂
    obtain ⟨ψ₁, hψA, hψ₁, -⟩ := hT.left ψ hψ k g m₂
    have hmem : ψ₁ ∈ genSpace L₁ ρ₁ J₁ := by
      refine SliceTensor.slice_mem ρ hJZ k₁ (T ψ) (hT.unipInv ψ hψ) hLv hC hZ g k m₂ ψ₁ hψA fun m₁ => ?_
      rw [hψ₁, infGL_comm, mul_assoc]
    have hls : ψ₁ ∈ lsF r s (T ψ) k g := ⟨m₂, fun m₁ => hψ₁ m₁⟩
    exact ⟨ψ₁, ⟨Submodule.subset_span hls, Submodule.subset_span hmem⟩, funext fun m₁ => hψ₁ m₁⟩
  have hb : ∀ κ : P, ∃ b ∈ Submodule.span ℂ (lsF r s (T ψ) k g), b.1 = (a κ : GA E r → ℂ) := by
    intro κ
    obtain ⟨b, hb, e⟩ := (a κ).2
    exact ⟨b, hb.1, e⟩
  choose b hbm hbe using hb
  have hright : ∀ κ : P, ∃ ψ₂ ∈ rsF r s (T ψ) k g, ∀ m₂, ψ₂.1 m₂ = f (κ.1, m₂) := by
    intro κ
    obtain ⟨ψ₂, -, e, -⟩ := hT.right ψ hψ k g κ.1
    exact ⟨ψ₂, ⟨κ.1, fun m₂ => e m₂⟩, e⟩
  choose q hqm hqe using hright
  have hf : ∀ m : GA E r × GA E s, f m = ∑ κ : P, (b κ).1 m.1 * (q κ).1 m.2 := by
    intro m
    have e := congrFun (ha _ (hleft m.2)) m.1
    rw [Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun κ _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hbe, hqe]
    ring
  let eP := (Fintype.equivFin P).symm
  refine ⟨Fintype.card P, fun i => b (eP i), fun i => q (eP i), fun i => hbm _, fun i => hqm _, fun m => ?_⟩
  rw [show (T ψ).1 (lev (Ad E) r s m * yp k g) = f m from rfl, hf m]
  exact (Equiv.sum_comp eP (fun κ => (b κ).1 m.1 * (q κ).1 m.2)).symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness


open LieSumUnipotentSlice PositivityTheory.Rg.Rs.SliceClasses in
theorem sliceU_of_noLog2 (hNL : NoLog) : SliceU := by
  intro E _ _ _ r s hr hs U hU hFG hSI hReg φ hφU c hc
  have hD := dict_holds
  have hFin := finTr_holds
  obtain ⟨F₀, hCT, F, hFspan, hFne, hFeig⟩ := hc
  have hAφ := hU.2 φ hφU
  obtain ⟨κ, -, rfl⟩ := ((hD E (r + s)).2.2.2 φ hAφ r hr (by omega)).2 F₀ hCT
  obtain ⟨cs, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hFspan
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℂ, b = fun t => cs t * κ := ⟨_, rfl⟩
  have hFval : ∀ g, F g = ∑ t ∈ cs.support, b t * An.ctn r φ.1 (aT E (r + s) r t * g) := by
    intro g
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hb, mul_assoc]

  obtain ⟨S, hSU, hSgen⟩ := hFG
  have hregψ : ∀ ψ ∈ U, ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL (Submodule.span ℂ {ψ}) τ m ∧ m.Nodup := by
    intro ψ hψ τ
    obtain ⟨m, ⟨hcard, hm⟩, hnd⟩ := hReg τ
    exact ⟨m, ⟨hcard, fun u χ hχ => hm u χ ((Submodule.span_singleton_le_iff_mem ψ U).2 hψ hχ)⟩, hnd⟩
  have hdec : ∀ ψ ∈ S, ∃ (C : Finset ℂ) (G : ℂ → GA E (r + s) → ℂ), An.ctn r ψ.1 = ∑ c ∈ C, G c ∧
      ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E (r + s) r t * g) = Complex.exp (c * t) * G c g := fun ψ hψ =>
    hNL E (r + s) r ψ (hU.2 ψ (hSU hψ)) (hSI ψ (hSU hψ)) (hregψ ψ (hSU hψ)) hr (by omega)
  choose! Cs Gs hsum hGeig using hdec
  obtain ⟨τs, a, ha⟩ := SliceUB2.lagrange (insert c (S.biUnion Cs)) c
  have ha1 : ∑ t ∈ τs, a t * Complex.exp (c * t) = 1 := by
    rw [ha c (Finset.mem_insert_self _ _), if_pos rfl]

  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring U hU.2 r τs a
  have hTval : ∀ ψ ∈ U, ∀ g, (T ψ).1 g = ∑ t ∈ τs, a t * An.ctn r ψ.1 (aT E (r + s) r t * g) := by
    intro ψ hψ g
    rw [hT ψ hψ, Aop_apply, ctSm_val r (hU.2 ψ hψ)]
  have hequiv : ∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ) := by
    intro o ψ hψ
    rw [hT _ (hU.1 o ψ hψ), hT ψ hψ, ctSm_act r (hU.2 ψ hψ) o (hU.2 _ (hU.1 o ψ hψ)), Aop_act]

  have hgen : ∀ ψ ∈ S, ∀ g, (T ψ).1 g = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
    intro ψ hψ g
    rw [hTval ψ (hSU hψ), hsum ψ hψ]
    calc ∑ t ∈ τs, a t * (∑ c' ∈ Cs ψ, Gs ψ c') (aT E (r + s) r t * g)
        = ∑ t ∈ τs, ∑ c' ∈ Cs ψ, a t * (Complex.exp (c' * t) * Gs ψ c' g) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c' hc' => by rw [hGeig ψ hψ c' hc']
      _ = ∑ c' ∈ Cs ψ, (∑ t ∈ τs, a t * Complex.exp (c' * t)) * Gs ψ c' g := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
          refine Finset.sum_congr rfl fun c' hc' => ?_
          rw [ha c' (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨ψ, hψ, hc'⟩))]

  let W : Submodule ℂ (Sm E (r + s)) :=
    { carrier := {ψ | ψ ∈ U ∧ ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g}
      add_mem' := fun {φ ψ} hφ hψ => ⟨U.add_mem hφ.1 hψ.1, fun t g => by
        simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, hφ.2 t g, hψ.2 t g, mul_add]⟩
      zero_mem' := ⟨U.zero_mem, fun t g => by simp⟩
      smul_mem' := fun b φ hφ => ⟨U.smul_mem b hφ.1, fun t g => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ.2 t g]
        ring⟩ }
  have hWst : _root_.GlobalTheory.CuspRep.IsStable W := by
    rintro o ψ ⟨hψ, he⟩
    refine ⟨hU.1 o ψ hψ, fun t g => ?_⟩
    have e1 : ltS (aT E (r + s) r t) (T ψ) = Complex.exp (c * t) • T ψ := Subtype.ext (funext fun g => he t g)
    have e2 := congrArg (fun G : Sm E (r + s) => G.1 g) (congrArg (act o) e1)
    simp only [← ltS_act, map_smul] at e2
    rw [hequiv o ψ hψ]
    exact e2
  have hSW : (↑S : Set (Sm E (r + s))) ⊆ W := by
    intro ψ hψ
    refine ⟨hSU hψ, fun t g => ?_⟩
    rw [hgen ψ hψ, hgen ψ hψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' hc' => ?_
    rw [hGeig ψ hψ c' hc']
    split_ifs with h
    · subst h
      ring
    · simp
  have hUW : U ≤ W := hSgen W hWst hSW
  have heig : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g :=
    fun ψ hψ => (hUW hψ).2

  have hTφ : T φ ≠ 0 := by
    intro h0
    have hz : ∀ g, ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g) = 0 := by
      intro g
      rw [← hTval φ hφU g, h0]
      rfl
    apply hFne
    funext g
    have hcomm : ∀ t t' : ℝ, aT E (r + s) r t' * (aT E (r + s) r t * g) =
        aT E (r + s) r t * (aT E (r + s) r t' * g) := by
      intro t t'
      rw [← mul_assoc, ← mul_assoc, ← aT_add, ← aT_add, add_comm t' t]
    calc F g = (∑ t' ∈ τs, a t' * Complex.exp (c * t')) * F g := by rw [ha1, one_mul]
      _ = ∑ t' ∈ τs, a t' * F (aT E (r + s) r t' * g) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t' _ => by rw [hFeig t' g]; ring
      _ = ∑ t ∈ cs.support, b t * ∑ t' ∈ τs, a t' * An.ctn r φ.1 (aT E (r + s) r t' * (aT E (r + s) r t * g)) := by
          simp_rw [hFval, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
          rw [hcomm]
          ring
      _ = 0 := by simp [hz]
  have hsplit : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (splitCentre E (r + s) t * g) = (T ψ).1 g := by
    intro ψ hψ t g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t (aT E (r + s) r u), mul_assoc,
      ctn_splitCentre (hSI ψ hψ)]
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ z : ℂ, ∀ ψ ∈ U, cap τ u ψ = z • ψ := by
    intro τ u
    obtain ⟨m, ⟨-, hm⟩, -⟩ := hReg τ
    exact ⟨_, hm u⟩
  refine ⟨T, ⟨hequiv, ⟨φ, hφU, hTφ⟩, ?_, ?_, ?_⟩, hTφ⟩
  · intro ψ hψ x g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    congr 1
    rw [← mul_assoc, hy, mul_assoc, ctn_unip (hU.2 ψ hψ)]
  · intro ψ hψ k g m₂
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).1 m₂
    refine ⟨χ, hχA, hχ, fun t m₁ => ?_, fun r₁ h1 h2 c₁ hc₁ =>
      ⟨ψ, hψ, exp_left hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) χ hχA m₂ _ hχ r₁ h1 h2 c₁ hc₁⟩⟩
    have e : lev (Ad E) r s (splitCentre E r t * m₁, m₂) = aT E (r + s) r t * lev (Ad E) r s (m₁, m₂) := by
      rw [show ((splitCentre E r t * m₁, m₂) : GA E r × GA E s) = (splitCentre E r t, 1) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_left r s r le_rfl]
    rw [hχ, hχ, e, mul_assoc, heig ψ hψ]
  · intro ψ hψ k g m₁
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).2 m₁
    refine ⟨χ, hχA, hχ, fun t m₂ => ?_, fun r₂ h1 h2 c₂ hc₂ =>
      ⟨ψ, hψ, exp_right hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) c (heig ψ hψ) χ hχA m₁ _ hχ
        r₂ h1 h2 c₂ hc₂⟩⟩
    have e : lev (Ad E) r s (m₁, splitCentre E s t * m₂) =
        splitCentre E (r + s) t * (aT E (r + s) r (-t) * lev (Ad E) r s (m₁, m₂)) := by
      rw [show ((m₁, splitCentre E s t * m₂) : GA E r × GA E s) = (1, splitCentre E s t) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_right r s s le_rfl, splitCentre_eq_aT, mul_assoc]
    rw [hχ, hχ, e, mul_assoc, hsplit ψ hψ, mul_assoc, heig ψ hψ]
    congr 2
    push_cast
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness

end
end
