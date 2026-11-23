module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open UpperTheory.V.Af.Smo (Eig)

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfEig :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfEig F := by
  intro F _ _ f hf v B h g
  let W (b : A F) (y : GL (Fin 2) (v.adicCompletion F)) :=
    f (gl (nU b) * (g * finGL F 2 (locGL F 2 v y)))
  have hW (b : A F) : Eig v B (W b) := by
    simpa only [W, mul_assoc] using h (gl (nU b) * g)
  have hi (y : GL (Fin 2) (v.adicCompletion F)) :
      IntegrableOn (fun b => W b y * ψ b) (fundamentalSet F) (adeleMeasure F) :=
    intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  change Eig v B (fun y => ∫ b in fundamentalSet F, W b y * ψ b ∂(adeleMeasure F))
  refine ⟨(h 1).card, fun y k hk => by simp only [fun b => (hW b).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hsupp := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm F v 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hsum (G : GL (Fin 2) (v.adicCompletion F) ⧸ GlobalTheory.LFun.KGL v (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c =
        ∑ c ∈ hsupp.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hsum]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have hb := (hW b).eig ϖ hϖ j hj y
  rw [hsum] at hb
  simp only [← mul_assoc, ← hb, Finset.sum_mul]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfBasic :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfBasic F := by
  intro F _ _ f hf
  have hc : ∀ {f : GL (Fin 2) (A F) → ℂ}, Lf f → ∀ g, IntegrableOn (fun b => f (gl (nU b) * g) * ψ b) (fundamentalSet F)
      (adeleMeasure F) := fun hf g => intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  refine ⟨?_, fun b g => ?_, hc hf, fun c g => ?_, fun f' hf' g => ?_⟩
  · obtain ⟨C, hC, hs⟩ := exists_cpt (F := F)
    have e : Wf f = fun g => ∫ b in C, f (gl (nU b) * g) * ψ b ∂((adeleMeasure F).restrict (fundamentalSet F)) := by
      funext g
      rw [Measure.restrict_restrict hC.measurableSet, Set.inter_eq_right.2 hs]; rfl
    rw [e]
    haveI : IsFiniteMeasure ((adeleMeasure F).restrict (fundamentalSet F)) :=
      isFiniteMeasure_restrict.2 (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_ne_top)
    set_option synthInstance.maxHeartbeats 200000 in
    exact continuous_parametric_integral_of_continuous
      ((hf.1.comp ((cont_n.comp continuous_snd).mul continuous_fst)).mul (cont_ψ.comp continuous_snd)) hC
  · unfold Wf
    rw [← integral_const_mul, ← int_add (h := fun x => ψ (-b) * (f (gl (nU x) * g) * ψ x))
      (fun k x => by rw [hf.per, ψ_add, ψ_rt, one_mul]) b]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : ψ (-b) * ψ (x + b) = ψ x := by rw [← ψ_add]; congr 1; ring
    simp only [n_add, mul_assoc]
    rw [mul_left_comm, this]
  · unfold Wf
    rw [← integral_const_mul]
    simp [mul_assoc]
  · unfold Wf
    rw [← integral_add (hc hf g) (hc hf' g)]
    simp [add_mul]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
theorem UpperTheory.ConvolutionTheory.R2.Pp.cuspZero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.CuspZero F := by
  intro F _ _ _ π f hf
  have hc : Continuous f.1 := by
    have hp : Continuous (TR.pInf F) := by
      have hc : Continuous (TR.infEq F).symm :=
        continuous_pi fun w =>
          (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
      exact hc.comp continuous_fst
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hm : Continuous fun x : GA F 2 => g⁻¹ * x := continuous_const.mul continuous_id
    have hI : Continuous (Matrix.GeneralLinearGroup.map (TR.pInf F) : GA F 2 → GL (Fin 2) (TR.Rinf F)) :=
      Continuous.units_map _ (continuous_id.matrix_map hp)
    have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin F) : GA F 2 → GL (Fin 2) (Af F)) :=
      Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
    have h1 : Continuous fun x : GA F 2 => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val :=
      (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (TR.Rinf F))).comp (hI.comp hm)
    have h2 : ContinuousAt (fun x : GA F 2 => TR.chart f.1 g (TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)) g :=
      ContinuousAt.comp (f := fun x : GA F 2 => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)
        (TR.contDiffAt_chart f.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
    refine h2.congr ?_
    have h3 : {x : GA F 2 | TR.finRep F 2 (Matrix.GeneralLinearGroup.map (pFin F) (g⁻¹ * x)) f = f} ∈ 𝓝 g :=
      ((π.cusp f hf).1.level.preimage (hFn.comp hm)).mem_nhds (by simp)
    filter_upwards [h3] with x hx
    rw [TR.chart_val]
    conv_lhs => rw [← hx]
    change f.1 (g * TR.infGL F 2 _ * finGL F 2 _) = _
    rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]
  refine ⟨⟨hc, (π.cusp f hf).1.left⟩, fun g => ?_⟩
  letI : Unique (BlockIx 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← int_one (ι := BlockIx 2 1)]
  have hz := (π.cusp f hf).2 1 one_pos one_lt_two (FourierWhittaker.vecMeasure F (BlockIx 2 1)) (FourierWhittaker.vecDomain F (BlockIx 2 1)) inferInstance (by exact FourierWhittaker.isAddFundamentalDomain_vecDomain) g
  rw [← hz]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : gl (nU (x default)) = unip x := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vn, unip, nilM]
    rfl
  simp only [this]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

private theorem irr_sub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) (W : Submodule ℂ V) (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  (h.eq_bot_or_eq_top (⟨W, fun g _ hv => hW g _ hv⟩ : Subrepresentation ρ)).imp
    (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)

theorem UpperTheory.ConvolutionTheory.R2.Pp.isotypQuot :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.IsotypQuot F := by
  intro F _ _ _ π v σ σ' h X _ _ ρ i hi hρ hs
  let T : Set (σ.V →ₗ[ℂ] X) := {j | ∀ g u, j (σ.ρ g u) = ρ g (j u)}
  let R : Submodule ℂ X := ⨆ j ∈ T, LinearMap.range j
  have hR : ∀ u, i u ∈ R := fun u => by
    refine Submodule.span_le.2 ?_ (hs u)
    rintro _ ⟨p, hp, x, rfl⟩
    refine (Submodule.span_le (p := R.comap p)).2 ?_ (isotyp F π v σ h x)
    rintro _ ⟨j, hj, z, rfl⟩
    exact Submodule.mem_iSup_of_mem (p ∘ₗ j) (Submodule.mem_iSup_of_mem (fun g u => by
      simp only [LinearMap.comp_apply, hj, hp]) ⟨z, rfl⟩)
  have irr := irr_sub σ.ρ σ.irred
  have irr' := irr_sub σ'.ρ σ'.irred
  obtain ⟨u₀, hu₀⟩ : ∃ u, i u ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hi (LinearMap.ext hn)
  obtain ⟨M, hM⟩ : ∃ M, Maximal (fun N : Submodule ℂ X => (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ i u₀ ∉ N) M := by
    refine (zorn_le_nonempty₀ {N : Submodule ℂ X | (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ i u₀ ∉ N}
      (fun c hc hch y hy => ⟨sSup c, ⟨fun g x hx => ?_, fun hx => ?_⟩,
      fun z hz => le_sSup hz⟩) ⊥ ⟨fun g x hx => by simp_all, by simpa using hu₀⟩).imp fun M hM => hM.2
    · obtain ⟨N, hN, h1⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx
      exact le_sSup hN ((hc hN).1 g x h1)
    · obtain ⟨N, hN, h1⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx
      exact (hc hN).2 h1
  obtain ⟨j, hj, hjM⟩ : ∃ j ∈ T, ¬ LinearMap.range j ≤ M := by
    by_contra hn
    push Not at hn
    exact hM.1.2 ((iSup₂_le hn : R ≤ M) (hR u₀))
  have hj' : ∀ g u, j (σ.ρ g u) = ρ g (j u) := hj
  have k1 : LinearMap.ker (M.mkQ ∘ₗ j) = ⊥ := (irr _ fun g u hu => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu ⊢
      rw [hj']; exact hM.1.1 g _ hu).resolve_right fun e => hjM (by
      rintro _ ⟨z, rfl⟩
      simpa using (e ▸ Submodule.mem_top : z ∈ LinearMap.ker (M.mkQ ∘ₗ j)))
  have k2 : LinearMap.ker (M.mkQ ∘ₗ i) = ⊥ := (irr' _ fun g u hu => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu ⊢
      rw [hρ]; exact hM.1.1 g _ hu).resolve_right fun e => hM.1.2 (by
      simpa using (e ▸ Submodule.mem_top : u₀ ∈ LinearMap.ker (M.mkQ ∘ₗ i)))
  have big : i u₀ ∈ M ⊔ LinearMap.range j := by
    by_contra hn
    refine hjM (le_sup_right.trans (hM.2 ⟨fun g x hx => ?_, hn⟩ le_sup_left))
    obtain ⟨m, hm, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), ← hj']
    exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩
  have hu0 : u₀ ≠ 0 := fun e => hu₀ (by rw [e, map_zero])
  have s1 : (M ⊔ LinearMap.range j).comap i = ⊤ := (irr' _ fun g u hu => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e⟩ := Submodule.mem_sup.1 hu
      rw [Submodule.mem_comap, hρ, ← e, map_add (f := _), ← hj']
      exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩).resolve_left fun e => hu0 (by
      have : u₀ ∈ (M ⊔ LinearMap.range j).comap i := big
      rwa [e, Submodule.mem_bot] at this)
  have s2 : (M ⊔ LinearMap.range i).comap j = ⊤ := (irr _ fun g u hu => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e⟩ := Submodule.mem_sup.1 hu
      rw [Submodule.mem_comap, hj', ← e, map_add (f := _), ← hρ]
      exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩).resolve_left fun e => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e'⟩ := Submodule.mem_sup.1 big
      have hz : z ∈ (M ⊔ LinearMap.range i).comap j := by
        rw [Submodule.mem_comap, eq_sub_of_add_eq' e', sub_eq_neg_add]
        exact Submodule.add_mem_sup (neg_mem hm) ⟨_, rfl⟩
      rw [e, Submodule.mem_bot] at hz
      rw [hz, map_zero, add_zero] at e'
      exact hM.1.2 (e' ▸ hm)
  have q : ∀ {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z] (a : Y →ₗ[ℂ] X) (b : Z →ₗ[ℂ] X),
      (M ⊔ LinearMap.range b).comap a = ⊤ → LinearMap.range (M.mkQ ∘ₗ a) ≤ LinearMap.range (M.mkQ ∘ₗ b) := by
    intro Y Z _ _ _ _ a b e
    rintro _ ⟨y, rfl⟩
    obtain ⟨m, hm, _, ⟨z, rfl⟩, e'⟩ := Submodule.mem_sup.1 (show y ∈ (M ⊔ LinearMap.range b).comap a from e ▸ Submodule.mem_top)
    exact ⟨z, by simp [← e', (Submodule.Quotient.mk_eq_zero M).2 hm]⟩
  have er := le_antisymm (q j i s2) (q i j s1)
  let e := (LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k1)).trans
    ((LinearEquiv.ofEq _ _ er).trans (LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k2)).symm)
  have he : ∀ u, (M.mkQ ∘ₗ i) (e u) = (M.mkQ ∘ₗ j) u := fun u =>
    congrArg Subtype.val ((LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k2)).apply_symm_apply _)
  refine ⟨e, fun g u => LinearMap.ker_eq_bot.1 k2 ?_⟩
  have h1 := he u
  rw [he]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1 ⊢
  rw [hj', hρ, ← map_sub]
  exact hM.1.1 g _ (by simpa using neg_mem h1)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfT :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfT F := by
  intro F _ _ f hf t g
  unfold Wf
  rw [← int_mul (h := fun x => f (gl (nU x) * (aE (IdeleGroup.diagonal F t) * g)) * ψ x)
    (fun k x => by rw [hf.per, ψ_add, ψ_rt, one_mul]) t]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  obtain ⟨γ, hγ⟩ := rat_a t
  have := a_n (IdeleGroup.diagonal F t) x
  simp only
  rw [← hf.2 γ (gl (nU x) * g), hγ, ← mul_assoc, ← mul_assoc, this]
  rfl
end
