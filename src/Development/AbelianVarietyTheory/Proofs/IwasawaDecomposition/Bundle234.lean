module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Mathlib.RingTheory.Regular.RegularSequence
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.TrueGeo.OfLattice

section Rect

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {B : LB X} {α β : Type} [Fintype α] [Fintype β]

def combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : Weight p σ B :=
  Weight.fs hB _ (fun _ => Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (secVal_mem _)) h

theorem combWeight_φ (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (i : B.ι) (y : CxPts p σ) :
    (combWeight hB s A h).φ i y = Real.log (∑ a, ‖∑ j, A j a * valR y.1 (B.U i) ((s j).f i)‖ ^ 2) := by
  simp only [combWeight, Weight.fs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem isCInf_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : (combWeight hB s A h).IsCInf := fun i y hy => by
  have hs : ContDiff ℝ ∞ fun v : α → ℂ => ∑ a, ‖∑ j, A j a * v j‖ ^ 2 :=
    ContDiff.sum fun a _ => (ContDiff.sum fun j _ =>
      contDiff_const.mul (contDiff_apply ℝ (fun _ => ℂ) j)).norm_sq ℂ
  refine ⟨B.U i, α, inferInstance, fun j => (s j).f i,
    fun v => Real.log (∑ a, ‖∑ j, A j a * v j‖ ^ 2), {v | ∑ a, ‖∑ j, A j a * v j‖ ^ 2 ≠ 0}, hy,
    isOpen_ne_fun hs.continuous continuous_const, ?_, hs.contDiffOn.log fun _ h => h,
    .of_forall fun z => combWeight_φ hB s A h i z⟩
  have := (h.sum_pos hy).ne'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this

theorem semiPosReg_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (D : ℕ) :
    (combWeight hB s A h).SemiPosReg D := fun i c y hy ξ => by
  let G (a : β) (v : V D) : ℂ := ∑ j, A j a * ev p σ _ ((s j).f i) (c.e.symm v)
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hG (a) : ContDiffAt ℂ 2 (G a) (c.e y) := ContDiffAt.sum fun j _ => contDiffAt_const.mul
    (((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho (c.holo _ ((s j).f i))).contDiffAt
      (ho.mem_nhds (mem_over c.e hy.1 hy.2))).of_le (by norm_cast))
  have e (v : V D) : ∑ a, Complex.normSq (G ((Fintype.equivFin β).symm a) v) = ∑ a, ‖G a v‖ ^ 2 :=
    (Equiv.sum_comp (Fintype.equivFin β).symm fun a => Complex.normSq (G a v)).trans
      (Finset.sum_congr rfl fun a _ => Complex.normSq_eq_norm_sq _)
  have h0 := h.sum_pos hy.2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  have := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (u := fun a v => Complex.normSq (G ((Fintype.equivFin β).symm a) v))
    (fun a => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun a => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _))
    (by rw [e]; simp only [G, c.e.left_inv hy.1]; exact h0) ξ
  simp only [e] at this
  simp only [combWeight_φ]
  exact this

variable [DecidableEq β]

theorem isConj_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ σ' : k →+* ℂ} {A A' : Matrix α β ℂ}
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j))
    (h' : Weight.NoCommonZero fun a => ∑ j, A' j a • secVal p σ' (s j)) {U : Matrix β β ℂ}
    (hU : U ∈ Matrix.unitaryGroup β ℂ) (e : A' = A.map (starRingEnd ℂ) * U) :
    (combWeight hB s A h).IsConj (combWeight hB s A' h') := fun i y y' hy' hy => by
  rw [combWeight_φ, combWeight_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((s j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((s j).f i)) :=
    CxPts.ev_conj hy' hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, A j a * valR y.1 (B.U i) ((s j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2

  simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
  Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

def combHerm (hB : B.IsLB) (s : α → B.Sec) (A : (k →+* ℂ) → Matrix α β ℂ)
    (h : ∀ σ, Weight.NoCommonZero fun a => ∑ j, A σ j a • secVal p σ (s j))
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup β ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) :
    HermLB p where
  B := B
  isLB := hB
  φ σ := combWeight hB s (A σ) (h σ)
  cInf σ := isCInf_combWeight hB s _ _
  conj σ σ' i y y' e hy := by
    obtain rfl := eq_conj_of_conj e
    obtain ⟨U, hU, e'⟩ := hc σ
    exact isConj_combWeight hB s (h σ) (h _) hU e' i y y' e hy

end Rect

theorem nefFib_of_isGenerated {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (L : HermLB p) (hL : IsGenerated L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have := hX.finite
  have : IsProper p := CommonModel.isProper_of_isProjOver hX.isProjOver
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hX.isProjOver
  have hA := hH.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 ((hL.pull i).isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable {F : Type} [Field F] [NumberField F]

section Values

variable {K : Type} [Field K] {Y : Var F} (y : Sp K ⟶ Y.X) {τ : F →+* K}




end Values

theorem injective_emb (σ : 𝓞 F →+* ℂ) : Function.Injective σ :=
  (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _))

def extEmb (σ : 𝓞 F →+* ℂ) : F →+* ℂ := IsFractionRing.lift (injective_emb σ)

theorem extEmb_comp (σ : 𝓞 F →+* ℂ) : (extEmb σ).comp (algebraMap (𝓞 F) F) = σ :=
  RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) (injective_emb σ) a

theorem extEmb_eq {σ : 𝓞 F →+* ℂ} {τ : F →+* ℂ} (h : τ.comp (algebraMap (𝓞 F) F) = σ) : extEmb σ = τ :=
  IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun ((extEmb_comp σ).trans h.symm) a

variable [StarRing F]




end GlobalTheory.TrueGeo.OfLattice
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.Twist RingTheory.Sequence
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Adelic

namespace GlobalTheory.CutDegree

section Sheaf

variable {X : Scheme.{0}} {L : LB X}

theorem injective_stalkLinear_cutHom (F : X.Modules) (hL : L.IsLB) (s : L.Sec) (i : L.ι) {x : X} (hx : x ∈ L.U i)
    (h : IsSMulRegular (F.presheaf.stalk x :) (X.presheaf.germ _ x hx (s.f i))) :
    Function.Injective (stalkLinear (cutHom F hL s) x) := by
  let e := stalkEquivOfLinear (F := twistZ F L (-1)) (G := F) (fun V hV => zchartEquiv hL (-1) i hV)
    (fun hV h' t => zchartEquiv_resM hL i hV h' t) hx
  have key : ⇑(stalkLinear (cutHom F hL s) x) = (X.presheaf.germ _ x hx (s.f i) • ·) ∘ e := funext fun u => by
    obtain ⟨V, hV, hxV, u, rfl⟩ := exists_germ_eq_of_mem hx u
    rw [stalkLinear_germ, cutHom_app F hL s i hV, QCoh.germ_smul, Function.comp_apply,
      stalkEquivOfLinear_germ _ _ hx hV]
    exact congrArg (· • _) (Cartier.germ_resG hV x hxV _)
  rw [key]
  exact h.comp e.injective

theorem nonempty_stalk_cut_equiv (F : X.Modules) (hL : L.IsLB) (s : L.Sec) (i : L.ι) {x : X} (hx : x ∈ L.U i) :
    Nonempty (QuotSMulTop (X.presheaf.germ _ x hx (s.f i)) (F.presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x]
      ((cut F hL s).presheaf.stalk x :)) := by
  refine ⟨(Submodule.quotEquivOfEq _ _ ?_).trans
    ((stalkLinear (cutπ F hL s) x).quotKerEquivOfSurjective (stalkLinear_surjective _ x))⟩
  ext t
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker]
  refine Iff.trans ?_ ((isMulBy_cutHom F hL s).stalkLinear_π_eq_zero_iff i hx t).symm
  simp

theorem topologicalKrullDim_le_zero_of_subset {T : Type} [TopologicalSpace T] {S : Finset T}
    (hc : ∀ x ∈ S, IsClosed ({x} : Set T)) {s : Set T} (hs : s ⊆ S) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := (S.finite_toSet.subset hs).to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 (hs x.2)).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

variable {k : Type} [Field k] (f : X ⟶ Sp k)

theorem interNum_sub_eq (hf : IsProjOver f) {F G : X.Modules} [IsFiniteQC F] [IsFiniteQC G] (φ : G ⟶ F) {d : ℕ}
    {P : Fin d → LB X} (hP : ∀ i, (P i).IsLB) :
    letI := algebraΓOfHom f
    interNum k F P - interNum k G P = interNum k (cokernel φ) P - interNum k (kernel φ) P := by
  letI := algebraΓOfHom f
  have := isNoetherian_of_isProjOver hf
  have fin : ∀ (H : X.Modules) [IsFiniteQC H], FiniteCohTwists k H := fun H _ =>
    finiteCohTwists_of_isProjOver (fun _ => rfl) H hf
  have h₁ := interNum_cokernel (kernel.ι φ) hP (fin _) (fin _)
  have h₂ := interNum_cokernel (kernel.ι (cokernel.π φ)) hP (fin _) (fin _)
  have e₁ : cokernel (kernel.ι φ) ≅ kernel (cokernel.π φ) := Abelian.coimageIsoImage φ
  have e₂ : cokernel (kernel.ι (cokernel.π φ)) ≅ cokernel φ :=
    (cokernelIsCokernel _).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (cokernel.π φ)))
  rw [interNum_congr k e₁] at h₁
  rw [interNum_congr k e₂] at h₂
  omega

theorem interNum_eq_sum_length (hf : IsProjOver f) (hL : L.IsLB) (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x))
    (S : Finset X) (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (l : List L.Sec) (F : X.Modules) [IsFiniteQC F]
    (hz : ∀ x ∈ support F, (∀ s ∈ l, x ∉ nonzeroLocus s) → x ∈ S)
    (hr : ∀ x ∈ S, IsWeaklyRegular (F.presheaf.stalk x :) (l.map fun s => X.presheaf.germ _ x (hc x) (s.f (c x)))) :
    letI := algebraΓOfHom f
    interNum k F (fun _ : Fin l.length => L) = (∑ x ∈ S, (Module.length (X.presheaf.stalk x)
      ((F.presheaf.stalk x :) ⧸ (Ideal.ofList (l.map fun s => X.presheaf.germ _ x (hc x) (s.f (c x))) • ⊤ :
        Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)))).toNat * f.residueDegree x : ℕ) := by
  letI := algebraΓOfHom f
  have := isNoetherian_of_isProjOver hf
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  induction l generalizing F with
  | nil =>
    have hs : support F ⊆ S := fun x hx => hz x hx (by simp)
    have hd : suppDim F ≤ 0 := topologicalKrullDim_le_zero_of_subset hS hs
    have : IsEmpty (Fin ([] : List L.Sec).length) := inferInstanceAs (IsEmpty (Fin 0))
    rw [interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k hd, hdim_zero_eq_sum_toNat f hd hs]
    refine congrArg _ <| Finset.sum_congr rfl fun x _ => ?_
    rw [(Submodule.quotEquivOfEqBot (Ideal.ofList [] • ⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :))
      (by simp only [Ideal.ofList_nil]; exact Submodule.bot_smul _)).length_eq.symm]
    rfl
  | cons s l ih =>
    have := isFiniteQC_twist (F := F) (isLB_lbZPow hL (-1))
    have e : (fun _ : Fin (s :: l).length => L) = (Fin.cons L (fun _ => L) : Fin (l.length + 1) → LB X) :=
      funext (Fin.cases rfl fun _ => rfl)
    have h0 : ∀ x ∈ S, Subsingleton ((kernel (cutHom F hL s)).presheaf.stalk x :) := fun x hx => by
      have h := injective_stalkLinear_cutHom F hL s (c x) (hc x) ((isWeaklyRegular_cons_iff _ _ _).1 (hr x hx)).1
      refine subsingleton_of_forall_eq 0 fun t => stalkLinear_injective (kernel.ι _) x (h ?_)
      rw [← LinearMap.comp_apply, ← stalkLinear_comp, kernel.condition, stalkLinear_zero, map_zero, map_zero]
      rfl
    have hK := ih (kernel (cutHom F hL s)) (fun x hx hl => ?_) fun x hx => ?_
    have hC := ih (cut F hL s) (fun x hx hl => ?_) fun x hx => ?_
    · rw [e, interNum_cons k F hL fun _ => hL, interNum_sub_eq f hf (cutHom F hL s) fun _ => hL, hK]
      rw [Finset.sum_eq_zero (fun x hx => ?_), Nat.cast_zero, sub_zero]
      · refine hC.trans (congrArg _ <| Finset.sum_congr rfl fun x _ => ?_)
        obtain ⟨q⟩ := nonempty_stalk_cut_equiv F hL s (c x) (hc x)
        rw [List.map_cons, (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner _ _ _).length_eq,
          (Submodule.Quotient.equiv _ _ q (by rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).length_eq]
      · have := h0 x hx
        rw [Module.length_eq_zero]
        simp
    · rw [support_cut] at hx
      exact hz x hx.1 (List.forall_mem_cons.2 ⟨hx.2, hl⟩)
    · obtain ⟨q⟩ := nonempty_stalk_cut_equiv F hL s (c x) (hc x)
      exact (q.isWeaklyRegular_congr _).1 ((isWeaklyRegular_cons_iff _ _ _).1 (hr x hx)).2
    · have h₁ := support_subset_of_mono (kernel.ι (cutHom F hL s)) hx
      rw [support_twist (isLB_lbZPow hL (-1))] at h₁
      refine hz x h₁ (List.forall_mem_cons.2 ⟨fun hs => notMem_support_iff.2 ?_ hx, hl⟩)
      have hu := (X.mem_basicOpen _ x (hc x)).1 ((Cartier.mem_nonzeroLocus_iff s _ (hc x)).1 hs)
      have h := injective_stalkLinear_cutHom F hL s (c x) (hc x) (hu.isSMulRegular _)
      refine subsingleton_of_forall_eq 0 fun t => stalkLinear_injective (kernel.ι _) x (h ?_)
      rw [← LinearMap.comp_apply, ← stalkLinear_comp, kernel.condition, stalkLinear_zero, map_zero, map_zero]
      rfl
    · have := h0 x hx
      exact ⟨fun _ _ _ _ _ => Subsingleton.elim _ _⟩

end Sheaf

section Algebra

variable {K R : Type} [Field K] [CommRing R]

end Algebra

section BaseChange

variable {k K : Type} [Field k] [Field K] {X X' : Scheme.{0}} {f : X ⟶ Sp k} {f' : X' ⟶ Sp K} {π : X' ⟶ X}
  {φ : k →+* K}

theorem ringKrullDim_stalk {d : ℕ} (h : SmoothOfRelativeDimension d f') {z : X'} (hz : IsClosed ({z} : Set X')) :
    ringKrullDim (X'.presheaf.stalk z) = d := by
  have := (StabFlat.stalk_of_smooth_local K X' f' d h z hz _ (Spec.map_preimage _).symm inferInstance).2.2.2
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot] at this
  exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).symm.trans this

end BaseChange

section Count

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} {f : X ⟶ Sp K} {L : LB X}

end Count

section Cut

variable {F : Type} [Field F] (Y : Var F) {Δ : Y.Dv} {n : ℕ} (b : Fin n → Y.H0 Δ)


end Cut

end GlobalTheory.CutDegree
end
end

section

set_option autoImplicit false

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign

theorem mContDiffAt_domGram {m r : ℕ} {k : WithTop ℕ∞} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : MContDiffAt k (domGram m r) x := by
  have h : MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) x := fun a b => by
    simp only [Matrix.of_apply]
    fun_prop
  exact (((mContDiffAt_const 1).sub (h.mul h.conjTranspose)).inv hx).transpose

theorem isUnit_det_domGram {m r : ℕ} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : IsUnit (domGram m r x).det := by
  rw [domGram, det_transpose]
  exact isUnit_nonsing_inv_det _ hx

theorem isNegSq_curv_of_changeFrame_comp {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n)
    (W : V n → Matrix (Fin m) (Fin m) ℂ) (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ) (hκ : 0 < κ)
    (hG : ∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ))
    (hZ : ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u)
    (hW : ∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u)
    (hWu : IsUnit (W v).det) (hpos : (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef)
    (hneg : IsNegSq (curv (domGram m r) (Z v)) r) : IsNegSq (curv G v) r := by
  obtain ⟨S, T, hS, hF⟩ := hneg
  have hu : IsUnit (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).det :=
    (isUnit_iff_isUnit_det _).1 hpos.isUnit
  have hD2 : MContDiffAt 2 (domGram m r) (Z v) := mContDiffAt_domGram _ hu
  have hDu : IsUnit (domGram m r (Z v)).det := isUnit_det_domGram _ hu
  have hZ2 : ContDiffAt ℂ 2 Z v := (GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hZ).contDiffAt
  have hW2 : MContDiffAt 2 W v := fun i j =>
    ((GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 (hW i j)).contDiffAt (n := 2)).restrict_scalars ℝ
  have hW0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar W x η = 0 := by
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hW i j]
      with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b)]
    rfl
  have hH2 : MContDiffAt 2 (fun x => domGram m r (Z x)) v :=
    fun a b => (hD2 a b).comp v (hZ2.restrict_scalars ℝ)
  have hK2 : MContDiffAt 2 (fun u => (W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ) v :=
    (hW2.transpose.mul hH2).mul hW2.conjTranspose.transpose
  have hKu : IsUnit ((W v)ᵀ * domGram m r (Z v) * (W v)ᴴᵀ).det := by
    simp only [det_mul, det_transpose, det_conjTranspose]
    exact (hWu.mul hDu).mul hWu.star
  refine ⟨S * W v, T ∘ₗ (fderiv ℂ Z v).toLinearMap, by rw [det_mul]; exact hS.mul hWu, fun ξ η => ?_⟩
  rw [curv_congr hG, curv_smul (f := fun _ => κ) contDiffAt_const hκ.ne' hK2 hKu, leviForm_const,
    curv_changeFrame (H := fun x => domGram m r (Z x)) hH2 hDu hW2 hWu hW0,
    curv_comp_holo hD2 hDu hZ2, hF, Matrix.mul_inv_rev]
  simp [Matrix.mul_assoc]

end GlobalTheory.PointFormSign
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecLinear

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem lieG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (hY : Y ∈ lieG G) : X + Y ∈ lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  have h2 : Yᴴ * G + G * Y = 0 := hY
  show (X + Y)ᴴ * G + G * (X + Y) = 0
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1, h2, add_zero]

theorem lieG_smul (a : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : a • X ∈ lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (a • X)ᴴ * G + G * (a • X) = 0
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]

theorem gard_add (hσ : IsURepOn (UJset ε) σ) {φ ψ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ)
    (w : H) : gard ε σ (φ + ψ) w = gard ε σ φ w + gard ε σ ψ w := by
  unfold gard
  rw [← integral_add (hφ.integrable (continuous_orbit hσ w)) (hψ.integrable (continuous_orbit hσ w))]
  simp only [Pi.add_apply, add_smul]

theorem gard_smul (a : ℝ) (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (w : H) :
    gard ε σ (a • φ) w = (a : ℂ) • gard ε σ φ w := by
  unfold gard
  rw [← integral_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Complex.coe_smul]

theorem dRep_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ w ∈ smSub G (trRep σ P), (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep (trRep σ P) (X + Y) w = dRep (trRep σ P) X w + dRep (trRep σ P) Y w) ∧ ∀ (a : ℝ), ∀ X ∈ lieG G, dRep (trRep σ P) (a • X) w = (a : ℂ) • dRep (trRep σ P) X w := by
  intro n ε H _ _ _ σ P G hP h hσ w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  refine ⟨fun X hX Y hY => ?_, fun a X hX => ?_⟩
  · refine sub_eq_zero.1 (eq_zero_of_inner_gard hσ fun φ hφ v => ?_)
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ hφ
    have hu := gard_mem hP h hσ hφ v
    rw [inner_sub_right, inner_add_right, inner_dRep hG hπ hu hw hX, inner_dRep hG hπ hu hw hY,
      inner_dRep hG hπ hu hw (lieG_add hX hY), (hψ X).2 hX, (hψ Y).2 hY, (hψ _).2 (lieG_add hX hY), map_add,
      gard_add hσ (hψ X).1 (hψ Y).1, inner_add_left]
    ring
  · refine sub_eq_zero.1 (eq_zero_of_inner_gard hσ fun φ hφ v => ?_)
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ hφ
    have hu := gard_mem hP h hσ hφ v
    rw [inner_sub_right, inner_smul_right, inner_dRep hG hπ hu hw hX,
      inner_dRep hG hπ hu hw (lieG_smul a hX), (hψ X).2 hX, (hψ _).2 (lieG_smul a hX), map_smul,
      gard_smul, inner_smul_left, Complex.conj_ofReal]
    ring

end GlobalTheory.SmVecLinear
end
