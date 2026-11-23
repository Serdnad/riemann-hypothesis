module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Formalism.LocalToGlobal.IndefiniteReal.DatumF

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.HSChoice.EtaleSection

namespace GlobalTheory.HSShort.EtaleSection

theorem spec_zero_iff {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (δ : ℕ)
    (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F) (hf : IsChowForm T.imageIdeal T.D δ f)
    (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) (ξ : Fin T.N → AlgebraicClosure E) :
    eval (fun p => ξ p.2) (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) = 0 ↔
      ∃ x ∈ T.geomPts E (T.linSection E s),
        ∑ j, ξ j * T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 j = 0 := by
  rw [eval_spec]
  obtain ⟨hA, hB⟩ := GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero F _ _ δ _ f hf
  have hs : ∀ (u y : Fin T.N → AlgebraicClosure E) (c : AlgebraicClosure E), ∑ j, u j * y j = 0 →
      ∑ j, u j * (c • y) j = 0 := fun u y c h => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum]
    rw [h, mul_zero]
  constructor
  · intro h0
    obtain ⟨y, hy, hc, h₁, h₂⟩ := hB _ _ _ h0
    obtain ⟨x₀, c, -, h⟩ := GlobalTheory.ConeOnto.exists_pt_of_mem_cone_of_isAlgClosed F T.toLinSys hT.alg.variety hT.alg.bpf _ y hy hc
    obtain ⟨x, rfl⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure E)).2 x₀
    refine ⟨x, (T.toLinSys.mem_subPts_cut_baseChange_iff E s x).2 fun i => ?_, ?_⟩ <;> rw [h]
    · exact hs _ _ _ (h₁ i)
    · exact hs _ _ _ h₂
  · rintro ⟨x, hx, h⟩
    refine hA _ _ _ _ (hT.alg.bpf.coords_ne_zero _) (fun g hg => ?_)
      ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx) h
    have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hg
    rwa [LinSys.baseHom_ptOver] at this

theorem simpleAt_of_noSquare : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → (δ : ℤ) = T.del → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite → T.InOpen E (T.linSection E s) → NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) → SimpleAt T δ f E s := by
  intro F _ _ T hT δ f hf hδ E _ _ s hfin hopen hsq
  classical
  obtain ⟨hfs, hmod, hrank⟩ := finite_finrank T hT E s hfin
  letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  haveI := hmod
  have hPfin : (T.geomPts E (T.linSection E s)).Finite := hfs.finite_subPts _
  have hcard := natCard_subPts _ _ hfs (AlgebraicClosure E)
  have hI := GlobalTheory.T.etale_of_finrank_le_card_algHom E Γ((T.linSection E s).subscheme, ⊤)
  set P := T.geomPts E (T.linSection E s) with hPdef
  set Ω := AlgebraicClosure E
  let yv : (T.toLinSys.baseChange E).Pt Ω → Fin T.N → Ω := fun x => T.coords (LinSys.toBase x : T.Pt Ω).1
  have hyv : ∀ x, yv x ≠ 0 := fun x => hT.alg.bpf.coords_ne_zero _
  let line : (T.toLinSys.baseChange E).Pt Ω → Submodule Ω (Fin T.N → Ω) := fun x => Submodule.span Ω {yv x}
  have : Finite (line '' P) := (hPfin.image line).to_subtype
  let eR : (line '' P) ≃ Fin (Nat.card (line '' P)) := Finite.equivFin _
  have hrep : ∀ q : Fin (Nat.card (line '' P)), ∃ x ∈ P, line x = (eR.symm q : Submodule Ω (Fin T.N → Ω)) :=
    fun q => (eR.symm q).2
  choose rep hrepP hrepl using hrep
  let y : Fin (Nat.card (line '' P)) → Fin T.N → Ω := fun q => yv (rep q)
  have hinj : ∀ q q', line (rep q) = line (rep q') → q = q' := by
    intro q q' h
    apply eR.symm.injective
    apply Subtype.ext
    rw [← hrepl, ← hrepl, h]
  have hzero : ∀ ξ : Fin T.N → Ω, eval (fun p => ξ p.2) (spec (fun i j => algebraMap E Ω (s i j)) f) = 0 ↔
      ∃ q, ∑ j, ξ j * y q j = 0 := by
    intro ξ
    rw [spec_zero_iff T hT δ f hf E s ξ]
    constructor
    · rintro ⟨x, hx, h0⟩
      obtain ⟨q0, hq0⟩ : ∃ q0, eR.symm q0 = ⟨line x, x, hx, rfl⟩ := ⟨_, eR.symm_apply_apply _⟩
      refine ⟨q0, ?_⟩
      have hl : line (rep q0) = line x := by rw [hrepl, hq0]
      have hm : y q0 ∈ line x := by
        rw [← hl]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
      rw [← ha]
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ a, ← Finset.mul_sum]
      rw [h0, mul_zero]
    · rintro ⟨q, hq⟩
      exact ⟨rep q, hrepP q, hq⟩
  have hprop : ∀ q q' (c : Ω), y q' = c • y q → q = q' := by
    intro q q' c h
    have hc : c ≠ 0 := by
      rintro rfl
      exact hyv _ (by simpa using h)
    apply hinj
    change Submodule.span Ω {yv (rep q)} = Submodule.span Ω {yv (rep q')}
    rw [show yv (rep q') = c • yv (rep q) from h, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  obtain ⟨hmδ, c, hc, hfac⟩ := HyperplaneFactor.eq_C_mul_prod_lin Ω T.N δ _ _ y
    (isHomogeneous_spec _ f hf.homog) hsq (fun q => hyv _) hprop hzero
  have hPf : Finite P := hPfin.to_subtype
  have hrepinj : Function.Injective (fun q => (⟨rep q, hrepP q⟩ : P)) := fun q q' h =>
    hinj q q' (by rw [show rep q = rep q' from congrArg Subtype.val h])
  have hfr : (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = δ := hrank.trans hδ.symm
  have h1 : Nat.card P = Nat.card (Γ((T.linSection E s).subscheme, ⊤) →ₐ[E] AlgebraicClosure E) := hcard
  have h3 : Module.finrank E Γ((T.linSection E s).subscheme, ⊤) = δ := by exact_mod_cast hfr
  have hPle : Nat.card P ≤ δ := by
    have h2 := hI.2.1
    omega
  have hmP : Nat.card (Fin (Nat.card (line '' P))) ≤ Nat.card P := Nat.card_le_card_of_injective _ hrepinj
  rw [Nat.card_fin] at hmP
  have hPδ : Nat.card P = δ := by omega
  have hbij : Function.Bijective (fun q => (⟨rep q, hrepP q⟩ : P)) :=
    hrepinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; show Nat.card P ≤ _; omega)
  refine ⟨⟨⟨hfs, etale_of_algebraEtale _ _ hfs (hI.2.2 ?_)⟩, hopen⟩, ?_, ?_, c, hc, ?_⟩
  · omega
  · rw [← Nat.card_coe_set_eq]
    exact hPδ
  · intro x hx x' hx' a ha h
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    obtain ⟨q', hq'⟩ := hbij.2 ⟨x', hx'⟩
    obtain rfl : rep q = x := congrArg Subtype.val hq
    obtain rfl : rep q' = x' := congrArg Subtype.val hq'
    obtain ⟨b, hb, e⟩ := T.toLinSys.exists_coords_baseChange E (rep q).1
    obtain ⟨b', hb', e'⟩ := T.toLinSys.exists_coords_baseChange E (rep q').1
    have e₁ : b' • y q' = a • b • y q := e'.symm.trans (h.trans (congrArg (a • ·) e))
    rw [hprop q q' (b'⁻¹ * a * b) (by rw [mul_smul, mul_smul, ← e₁, inv_smul_smul₀ hb'])]
  · rw [hfac]
    congr 1
    rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
    refine finprod_mem_eq_of_bijOn rep ⟨fun q _ => hrepP q, fun q _ q' _ h => hinj q q' (by rw [h]), fun x hx => ?_⟩
      fun q _ => rfl
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨q, Set.mem_univ _, congrArg Subtype.val hq⟩

end GlobalTheory.HSShort.EtaleSection
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SBClosure

open scoped Topology

theorem nonarch_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, AddCommGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup (G i)),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

theorem eq_smul_indicator_closure {X : Type} [AddCommGroup X] [TopologicalSpace X] [NonarchimedeanAddGroup X]
    (S : AddSubgroup X) (B : Set X) (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hf0 : f ≠ 0) (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB X, (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) → ∃ c : ℂ, g = c • f) :
    ∃ c : ℂ, f = c • (closure (S : Set X)).indicator 1 ∧ IsOpen (closure (S : Set X)) ∧
      IsCompact (closure (S : Set X)) := by
  set H : AddSubgroup X := S.topologicalClosure with hHdef
  have hHc : (H : Set X) = closure (S : Set X) := rfl
  rw [← hHc]
  have hcont : Continuous f := hf.1.continuous
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (funext h)
  have hind : ∀ U : Set X, IsClopen U → ∀ φ ∈ GlobalTheory.WeilM.SB X, U.indicator φ ∈ GlobalTheory.WeilM.SB X := by
    intro U hU φ hφ
    have : U.indicator φ = U.indicator 1 * φ := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [this]
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩
  have hSH : S ≤ H := S.le_topologicalClosure
  have hHcl : IsClosed (H : Set X) := S.isClosed_topologicalClosure
  have hH : ∀ h ∈ H, f (Y₀ + h) = f Y₀ := by
    intro h hh
    have hcl : IsClosed {h : X | f (Y₀ + h) = f Y₀} :=
      isClosed_eq (hcont.comp (continuous_const.add continuous_id)) continuous_const
    have hS : (S : Set X) ⊆ {h : X | f (Y₀ + h) = f Y₀} := fun s hs => hinv s hs Y₀
    exact (closure_minimal hS hcl) hh
  have hW : ∀ x, f x ≠ 0 → x - Y₀ ∈ H := by
    intro x hx
    by_contra hxH
    have hopen : (H : Set X)ᶜ ∈ 𝓝 (x - Y₀) := hHcl.isOpen_compl.mem_nhds hxH
    have h0 : (fun u => x - Y₀ + u) ⁻¹' (H : Set X)ᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      simpa using hopen
    obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    set V : AddSubgroup X := H ⊔ U.toAddSubgroup with hVdef
    have hVo : IsOpen (V : Set X) := AddSubgroup.isOpen_mono (le_sup_right : U.toAddSubgroup ≤ V) U.isOpen
    have hVc : IsClosed (V : Set X) := AddSubgroup.isClosed_of_isOpen V hVo
    have hxV : x - Y₀ ∉ V := by
      intro hm
      obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hm
      have hb' : -b ∈ U := U.neg_mem hb
      have := hU hb'
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe] at this
      apply this
      rw [← hab]
      simpa using ha
    set Wset : Set X := (fun y => y - Y₀) ⁻¹' (V : Set X) with hWdef
    have hWc : IsClopen Wset :=
      ⟨hVc.preimage (continuous_id.sub continuous_const), hVo.preimage (continuous_id.sub continuous_const)⟩
    have hWinv : ∀ s ∈ S, ∀ Y, (Y + s ∈ Wset ↔ Y ∈ Wset) := by
      intro s hs Y
      have hsV : s ∈ V := AddSubgroup.mem_sup_left (hSH hs)
      simp only [Wset, Set.mem_preimage, SetLike.mem_coe]
      rw [show Y + s - Y₀ = (Y - Y₀) + s by abel]
      exact V.add_mem_cancel_right hsV
    obtain ⟨c, hc⟩ := huniq (Wset.indicator f) (hind _ hWc f hf) (by
      intro s hs Y
      by_cases hY : Y ∈ Wset
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem ((hWinv s hs Y).mpr hY), hinv s hs Y]
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY ((hWinv s hs Y).mp h))]) (by
      intro Y hY
      by_cases h : Y ∈ Wset
      · rw [Set.indicator_of_mem h, hsupp Y hY]
      · rw [Set.indicator_of_notMem h])
    have e1 := congrFun hc Y₀
    have e2 := congrFun hc x
    have hY₀W : Y₀ ∈ Wset := by simp [Wset, V.zero_mem]
    rw [Set.indicator_of_mem hY₀W] at e1
    rw [Set.indicator_of_notMem (show x ∉ Wset from hxV)] at e2
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    have hc1 : c = 1 := by
      have : (c - 1) * f Y₀ = 0 := by rw [sub_mul, ← e1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hY₀)
    rw [hc1, one_mul] at e2
    exact hx e2.symm
  have hHeq : (H : Set X) = (fun h => Y₀ + h) ⁻¹' {y | f y ≠ 0} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro hh; rw [hH h hh]; exact hY₀
    · intro hne; simpa using hW _ hne
  have hHo : IsOpen (H : Set X) := by
    rw [hHeq]
    exact (isOpen_compl_singleton.preimage hcont).preimage (continuous_const.add continuous_id)
  have hHk : IsCompact (H : Set X) := by
    have hK : IsCompact ((fun h => Y₀ + h) ⁻¹' tsupport f) :=
      (Homeomorph.addLeft Y₀).isCompact_preimage.mpr hf.2
    refine hK.of_isClosed_subset hHcl ?_
    intro h hh
    exact subset_tsupport f (by rw [Function.mem_support, hH h hh]; exact hY₀)
  have hHclo : IsClopen (H : Set X) := ⟨hHcl, hHo⟩
  have h1SB : (H : Set X).indicator (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
    refine ⟨?_, HasCompactSupport.intro' hHk hHcl fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant X ℂ) hHclo).isLocallyConstant
    convert this using 1
    funext x
    first
    | rfl
    | by_cases hx : x ∈ (H : Set X) <;> simp [hx, LocallyConstant.indicator]
  obtain ⟨c, hc⟩ := huniq _ h1SB (by
      intro s hs Y
      have : (Y + s ∈ (H : Set X) ↔ Y ∈ (H : Set X)) := H.add_mem_cancel_right (hSH hs)
      by_cases hY : Y ∈ (H : Set X)
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (this.mpr hY)]; rfl
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (this.mp h))]) (by
      intro Y hY
      refine Set.indicator_of_notMem (fun hYH => hY ?_) _
      have hB0 : Y₀ ∈ B := by
        by_contra h; exact hY₀ (hsupp _ h)
      have hB1 : Y₀ + Y ∈ B := by
        by_contra h; exact hY₀ ((hH Y hYH).symm.trans (hsupp _ h))
      exact hB _ _ hB0 hB1)
  have e0 := congrFun hc 0
  rw [Set.indicator_of_mem (show (0 : X) ∈ (H : Set X) from H.zero_mem)] at e0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at e0
  have hc0 : c ≠ 0 := by
    rintro rfl; simp at e0
  refine ⟨c⁻¹, ?_, hHo, hHk⟩
  funext y
  have ey := congrFun hc y
  simp only [Pi.smul_apply, smul_eq_mul] at ey ⊢
  rw [ey, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory.SBClosure

theorem GlobalTheory.SBClosure.main : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {m k : ℕ}
    (S : AddSubgroup (Matrix (Fin m) (Fin k) (Fv F v))) (B : Set (Matrix (Fin m) (Fin k) (Fv F v)))
    (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : Matrix (Fin m) (Fin k) (Fv F v) → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB _) (hf0 : f ≠ 0)
    (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin k) (Fv F v)), (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) →
      ∃ c : ℂ, g = c • f),
    ∃ c : ℂ, f = c • (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))).indicator 1 ∧
      IsOpen (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) ∧ IsCompact (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) := by
  intro F _ _ v m k S B hB f hf hf0 hinv hsupp huniq
  haveI : NonarchimedeanAddGroup (Fin k → Fv F v) := GlobalTheory.SBClosure.nonarch_pi (fun _ : Fin k => Fv F v)
  haveI : NonarchimedeanAddGroup (Matrix (Fin m) (Fin k) (Fv F v)) :=
    GlobalTheory.SBClosure.nonarch_pi (fun _ : Fin m => Fin k → Fv F v)
  exact GlobalTheory.SBClosure.eq_smul_indicator_closure S B hB f hf hf0 hinv hsupp huniq
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchwartzTranslation

theorem schA_add_const : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : κ → AF F),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun y => Φ (y + c)) ∈ GlobalTheory.WeilM.schA F κ :=
  fun {F} _ _ {_} _ c Φ hΦ => GlobalTheory.SchwartzTranslate.schA_translate F c hΦ

end GlobalTheory.SchwartzTranslation
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_nonneg_adelicSchwartz_bump_test : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : Set (κ → AF F)), U ∈ nhds 0 →
    ∃ Φ ∈ schA F κ, Continuous Φ ∧ (∀ x, Φ x ≠ 0 → x ∈ U) ∧ (∀ x, (Φ x).im = 0 ∧ 0 ≤ (Φ x).re) ∧ Φ 0 = 1 := by
  first | exact @GlobalTheory.AdelicBumpTest.exists_nonneg_test | exact GlobalTheory.AdelicBumpTest.exists_nonneg_test | (intros; apply GlobalTheory.AdelicBumpTest.exists_nonneg_test <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.AffineCurve

theorem subsingleton_of_three_le : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n →
    Subsingleton (Ht q (sp B) n i) := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · exact GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B (GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB) (tw q i) n (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    suffices h : ∀ x : Ht q (sp B) (m + 1) i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
    intro x
    obtain ⟨_, _⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    have h1 : pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 :=
      (GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK (m + 1) i (by omega)).elim _ _
    obtain ⟨f, hf0, hfu, hxf⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB (m + 1) i x h1
    obtain ⟨A', _, _, _, hA', hxA'⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf0 hfu (m + 1) i (by omega) x
    obtain ⟨δ, hex, hkill⟩ := GlobalTheory.T.mayer_vietoris_exact_etale q B A' f hA' m i
    obtain ⟨z, rfl⟩ := (hex x).mp (by simp [hxf, hxA'])
    obtain ⟨A'', _, _, _, φ, hA'', hz⟩ := GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood q k B hq f hf0 hfu A' hA' m i (by omega) z
    exact hkill A'' φ hA'' z hz

end GlobalTheory.EtC.AffineCurve
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_tateTwistCohomology_two_subsingleton : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ,
    Subsingleton (Ht q (sp B) 2 i) := by
  intro q _ k B _ _ _ _ _ _ hq i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)).ne'
  have hζ : ∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨algebraMap k B z, ?_⟩
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic,
      hz.eq_zero, map_zero]
  obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q B hqB hζ 2 i 1
  have h0 : ∀ x : Ht q (sp B) 2 1, x = 0 := by
    intro x
    obtain ⟨f, hf, hxf⟩ := GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two q k B hq 1 x
    obtain ⟨A', _, _, hA', hxA'⟩ := GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass q k B hq f hf 2 1 (by norm_num) x
    obtain ⟨w, hw⟩ := GlobalTheory.T.etaleExcision_vanishing_under_refinement q B A' f hA' 1 1 x hxf hxA'
    obtain ⟨g, hfg, A₂, C, _, _, _, _, _, _, h2, hg, hC, a, haC, hwa⟩ := GlobalTheory.T.exists_kummerClass_agreeing_near_zeros q k B hq f hf A' hA' w
    exact hw g hfg A₂ C h2 hg hC a haC hwa
  exact ⟨fun a b => e.injective (by rw [h0 (e a), h0 (e b)])⟩

end GlobalTheory.EtC
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

theorem _root_.GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport : GlobalTheory.PsCo.Pc1.StShape := by
  first | exact @GlobalTheory.ShapeSmoothFinite.stShape | exact GlobalTheory.ShapeSmoothFinite.stShape | (intros; apply GlobalTheory.ShapeSmoothFinite.stShape <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_reproducingPolynomial_valueAtOne_maxCompact : GlobalTheory.PsCo.Pc3.Repro := by
  first | exact @GlobalTheory.PsCo.Pc3.fock_reproducing_formula | exact GlobalTheory.PsCo.Pc3.fock_reproducing_formula | (intros; apply GlobalTheory.PsCo.Pc3.fock_reproducing_formula <;> assumption)
end
