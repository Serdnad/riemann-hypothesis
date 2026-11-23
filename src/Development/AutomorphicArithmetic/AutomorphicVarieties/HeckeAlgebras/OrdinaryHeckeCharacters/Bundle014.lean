module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle089
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle086
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle087
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem coreSep_coord {A M N κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module ℂ N]
    (Y : Submodule A M) (φ : A →+* ℂ) (sp : M → N) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = φ b • sp f) (b : Module.Basis κ A Y)
    (hind : LinearIndependent ℂ fun i => sp (b i)) (g : Y) (hg : sp g = 0) (i : κ) : φ (b.repr g i) = 0 := by
  classical
  let s : Y →ₛₗ[φ] N :=
    { toFun := fun f => sp f
      map_add' := fun f f' => hadd _ f.2 _ f'.2
      map_smul' := fun r f => hsmul _ f.2 r }
  have h1 : s g = ∑ j ∈ (b.repr g).support, φ (b.repr g j) • sp (b j) := by

    conv_lhs => rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => s.map_smulₛₗ _ _
  by_cases hi : i ∈ (b.repr g).support
  · exact linearIndependent_iff'.1 hind _ (fun j => φ (b.repr g j)) (h1.symm.trans hg) i hi
  · rw [Finsupp.notMem_support_iff.1 hi, map_zero]

private theorem coreSep_kill {N J : Type*} [AddCommGroup N] [Module ℂ N] (E : Submodule ℂ N) (Y : J → Submodule ℂ N)
    (hE : E = ⨆ j, Y j ⊓ E) (T : Module.End ℂ E) (h : ∀ j, ∀ F : E, (F : N) ∈ Y j → T F = 0) (F : E) : T F = 0 := by
  have hle : E ≤ (LinearMap.ker T).map E.subtype := by
    conv_lhs => rw [hE]
    exact iSup_le fun j G hG => ⟨⟨G, hG.2⟩, h j ⟨G, hG.2⟩ hG.1, rfl⟩
  obtain ⟨G, hG, hGF⟩ := hle F.2
  have : G = F := Subtype.ext hGF
  exact this ▸ hG

theorem UpperTheory.V.Hi.coreSep :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ lam ∈ H.admitted, H.DenseWt θ lam → ∀ t : H.TK θ a K, (∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Good θ (x.toRingHom.comp (algebraMap A _)) lam → x t = 0) → t = 0 := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι P hP a K _ lam hlam hD t ht
  obtain ⟨-, -, hfree, -⟩ := hiComm L Ω l n c H hAx A θ hθ K
  let b := Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K))
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  let g : H.X.Ord (H.τA A) θ (H.lev K) :=
    ⟨((t : Module.End A (H.MK θ a K)) f : H.MK θ a K), ((t : Module.End A (H.MK θ a K)) f).2.1⟩
  have hg : g = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine hD _ fun x hx => ?_
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hAx A θ hθ ι x lam hx.2.1
    obtain ⟨h1, act, h2, -, -, -, h3⟩ := partAct0 hLit L Ω l n c H hAx A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
    have hE := h1.resolve_right (not_not.2 hx)
    have h0 := coreSep_kill _ _ hE (act t) (fun Y F hF => by
      by_cases hb : Y.1.Y ⊓ Submodule.span ℂ (sp '' H.MK θ a K) = ⊥
      · have : F = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb _ ⟨hF, F.2⟩)
        rw [this, map_zero]
      · obtain ⟨y, hy, hact⟩ := h3 hx Y.1 hb
        rw [hact t F hF, ht y (hy ▸ hx), map_zero, zero_smul])
      ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩
    have h4 := h2 t f ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩ rfl
    rw [h0] at h4
    have h5 := coreSep_coord _ (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) b (hsp.indep K _ b) g h4.symm i
    exact ι.injective (h5.trans (map_zero ι).symm)
  exact Subtype.ext (congrArg (fun z : H.X.Ord (H.τA A) θ (H.lev K) => (z : H.X.Fn A H.m)) hg)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem fu_patch {G ι : Type} [Group G] [Finite ι] {H : ι → Type} [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (P : Subgroup G) (b : ∀ i, H i) (h : ∀ i, ∃ y ∈ P, p i y = b i ∧ ∀ j, j ≠ i → p j y = 1) :
    ∃ y ∈ P, ∀ i, p i y = b i := by
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ T : Finset ι, ∃ y ∈ P, (∀ i ∈ T, p i y = b i) ∧ ∀ i ∉ T, p i y = 1 := fun T => by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by simp, fun i _ => map_one _⟩
    | insert a T ha ih =>
      obtain ⟨y, hy, h1, h2⟩ := ih
      obtain ⟨z, hz, h3, h4⟩ := h a
      refine ⟨y * z, mul_mem hy hz, fun i hi => ?_, fun i hi => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · rw [map_mul, h2 _ ha, h3, one_mul]
        · rw [map_mul, h1 i hi, h4 i (fun e => ha (e ▸ hi)), mul_one]
      · rw [Finset.mem_insert, not_or] at hi
        rw [map_mul, h2 i hi.2, h4 i hi.1, mul_one]
  obtain ⟨y, hy, h1, -⟩ := key Finset.univ
  exact ⟨y, hy, fun i => h1 i (Finset.mem_univ i)⟩

section

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ}

private theorem fu_under (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [← s.hA v x, IsScalarTower.algebraMap_apply (Lp L) L Ω]
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm

omit [Fact l.Prime] [IsCMField L] in
private theorem fu_l (w : Plc L) : ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L)) l]
  rfl

open scoped Pointwise in
private theorem fu_split (V : s.Lev) (w : Plc L) (hw : w.under (𝓞 (Lp L)) ∈ V.S') : IsSplitAt w := by
  by_contra hn
  have uq : ∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → u = w := fun u hu => by
    by_contra h
    exact hn ⟨u, h, hu⟩
  have hA := s.hw (w.under (𝓞 (Lp L)))
  rw [uq _ (fu_under s _)] at hA
  have hD := V.split _ hw
  generalize s.A (w.under (𝓞 (Lp L))) = A at hA hD
  let τ : L ≃ₐ[Lp L] L := s.c.restrictNormal L
  have hl : IsLift τ.toRingEquiv s.c.toRingEquiv := fun x => (AlgEquiv.restrictNormal_commutes s.c L x).symm
  have h1 : IsPlaceOver (s.c⁻¹ • A) (preplace τ.toRingEquiv w) :=
    isPlaceOver_preplace hl (fun x => (ValuationSubring.mem_inv_pointwise_smul_iff (g := s.c) (S := A) (x := x)).symm) hA
  rw [uq (preplace τ.toRingEquiv w) (HeightOneSpectrum.ext (Ideal.ext fun x => by
    change RingOfIntegers.mapRingEquiv τ.toRingEquiv (algebraMap _ (𝓞 L) x) ∈ w.asIdeal ↔ algebraMap _ (𝓞 L) x ∈ w.asIdeal
    rw [show RingOfIntegers.mapRingEquiv τ.toRingEquiv (algebraMap _ (𝓞 L) x) = algebraMap _ (𝓞 L) x from
      Subtype.ext (τ.commutes x)]))] at h1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := L) hA h1
  have h2 : s.c * W.resP L Ω g ∈ Dec (F := Lp L) A := by
    refine mem_Dec.2 ?_
    have h3 : W.resP L Ω g • A = s.c⁻¹ • A := hg
    rw [mul_smul, h3, smul_inv_smul]
  have h4 : s.c ∈ (W.resP L Ω).range := (mul_mem_cancel_right (MonoidHom.mem_range.2 ⟨g, rfl⟩)).1 (hD h2)
  have h5 := (V.hη _).2 h4
  rw [V.η_c] at h5
  exact absurd h5 (by decide)

private theorem fu_cmp {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (g : UA L n) :
    cmp n w ((away l L n).rangeRestrict g) = cLoc w g := by
  rw [CaseU.cmp, dite_eq_left h]
  rfl

private theorem fu_cmp_mem (w : Plc L) (g : UA L n) {P : Subgroup (GLw n w)} (hg : cLoc w g ∈ P) :
    cmp n w ((away l L n).rangeRestrict g) ∈ P := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
  · rw [CaseU.cmp, dite_eq_right (not_not.2 h)]
    exact one_mem _
  · rwa [fu_cmp h]

private theorem fu_open : IsOpen ((⨅ w : Plc L, (KO (w.adicCompletion L) (Fin n)).comap (cLoc w) : Subgroup (UA L n)) : Set (UA L n)) := by
  let p : UA L n →* GL (Fin n) (Af L) := (Matrix.GeneralLinearGroup.map (pFin L)).comp (UA L n).subtype
  have hp : Continuous p := GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val
  have ho : IsOpen (GlobalTheory.GLIntegral.intSubring L : Set (Af L)) := RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 L) => (v.adicCompletionIntegers L : Set (v.adicCompletion L)))
    (fun v => Valued.isOpen_valuationSubring _)
  refine Subgroup.isOpen_mono (H₁ := (GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring L)).comap p) (fun g hg => ?_)
    ((GlobalTheory.GLIntegral.isOpen_glSub _ ho).preimage hp)
  have hv : ∀ (w : Plc L) (x : w.adicCompletion L), x ∈ w.adicCompletionIntegers L → x ∈ 𝒪[w.adicCompletion L] := fun w x hx => by
    haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
    exact hx
  exact Subgroup.mem_iInf.2 fun w => (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => hv w _ (hg.1 i j w), fun i j => hv w _ (hg.2 i j w)⟩

end

private theorem fu_Kc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    IsOpen (Kc k n 1 : Set (GL (Fin n) k)) := by
  have key : ∀ I : Ideal 𝒪[k], I = maximalIdeal 𝒪[k] → (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker =
      (Matrix.GeneralLinearGroup.map (n := Fin n) (residue 𝒪[k])).ker := by
    rintro _ rfl
    rfl
  rw [Kc, key _ (pow_one _)]
  exact GlobalTheory.StepData.isOpen_KOne

private theorem fu_Iw {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] (S : V → Plc L) (b : GV n S)
    (hb : ∀ v, b v ∈ (glIwa ((S v).adicCompletion L) n).I1 0) : b ∈ (iwS n S).Iw 0 := by
  choose x hx t ht y hy e using fun v => (iwMem _ _ 0 _).2.1.1 (hb v)
  rw [show b = x * t * y from funext e]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left fun v _ => hx v))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right fun v _ => (glIwa _ n).Tc_le 0 (ht v))))
    (Subgroup.mem_sup_right fun v _ => hy v)

private theorem fu_iInf {G ι : Type} [Group G] [TopologicalSpace G] [Finite ι] (H : ι → Subgroup G)
    (h : ∀ i, IsOpen (H i : Set G)) : IsOpen ((⨅ i, H i : Subgroup G) : Set G) := by
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite h

theorem UpperTheory.V.Hi.finU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ K, (hset Q τ₀).X.FinLevel ((hset Q τ₀).lev K) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K
  classical
  let Φ : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  have hsurj : Function.Surjective Φ := by
    rintro ⟨a, b⟩
    obtain ⟨g, rfl⟩ := (away l L n).rangeRestrict_surjective a
    obtain ⟨y, hy, h1⟩ := fu_patch (fun v : V.frame.Vl => cLoc (n := n) (s.w v.1)) (away l L n).ker
      (fun v => (cLoc (s.w v.1) g)⁻¹ * b v) fun v => by
        obtain ⟨j, hj, h2, -⟩ := (secU l L Ω s n hn (s.w v.1)
          (fu_split V _ (by rw [fu_under]; exact V.sub (Or.inl v.2)))).1
        have h3 : ∀ x, ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ v.1 → cLoc u (j x) = 1 := fun x u hu =>
          Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (hj x)).2 u) (by rwa [fu_under])
        refine ⟨j _, funext fun u => h3 _ u.1 fun e => u.2 (fu_l u.1 |>.1 (e ▸ v.2)), h2 _, fun v' hv => h3 _ _ ?_⟩
        rw [fu_under]
        exact fun e => hv (Subtype.ext e)
    refine ⟨g * y, Prod.ext (Subtype.ext ?_) (funext fun v => ?_)⟩
    · change away l L n (g * y) = away l L n g
      rw [map_mul, MonoidHom.mem_ker.1 hy, mul_one]
    · change cLoc (s.w v.1) (g * y) = b v
      rw [map_mul, h1 v, mul_inv_cancel_left]
  have hinf : ∀ x ∈ infU L n, Φ x = 1 := fun x hx => by
    have h1 : ∀ w, cLoc w x = 1 := fun w => by
      have h2 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
      change Matrix.GeneralLinearGroup.map (pLoc L w) (Matrix.GeneralLinearGroup.map (pFin L) x.1) = 1
      rw [h2, map_one]
    exact Prod.ext (Subtype.ext (funext fun w => h1 w.1)) (funext fun v => h1 _)
  let K0 : Subgroup (UA L n) := ((⨅ w : Plc L, (KO (w.adicCompletion L) (Fin n)).comap (cLoc w)) ⊓
    (Kc _ n 1).comap (cLoc (s.w s.v0))) ⊓ ((⨅ q : Q.Q, Subgroup.comap (cLoc (Q.wq q)) (K.1 q)) ⊓
    ⨅ v : V.frame.Vl, ((glIwa ((s.w v.1).adicCompletion L) n).I1 0).comap (cLoc (s.w v.1)))
  have ho : IsOpen (K0 : Set (UA L n)) := by
    refine (fu_open.inter ((fu_Kc n).preimage (GlobalTheory.DefU.Inert.continuous_cLoc _))).inter (IsOpen.inter ?_ ?_)
    · exact fu_iInf _ fun q => (K.2 q).1.preimage (GlobalTheory.DefU.Inert.continuous_cLoc _)
    · exact fu_iInf _ fun v => ((glBridge _ n ℂ 1).2.2.1 0).1.preimage (GlobalTheory.DefU.Inert.continuous_cLoc _)
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite L n (K0.comap (GlobalTheory.UnitaryBC.finU (E := L) (n := n)).subtype)
    (ho.preimage continuous_subtype_val)
  refine ⟨S.image Φ, fun g => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj g
  obtain ⟨γ, hγ, x, hx, z, hz, k, ⟨⟨hk1, hk2⟩, hk3, hk4⟩, rfl⟩ := hS g
  replace hk1 : ∀ w : Plc L, cLoc w k.1 ∈ KO (w.adicCompletion L) (Fin n) := Subgroup.mem_iInf.1 hk1
  replace hk3 : ∀ q : Q.Q, cLoc (Q.wq q) k.1 ∈ K.1 q := Subgroup.mem_iInf.1 hk3
  let u : Ub n s := ⟨(away l L n).rangeRestrict k.1, Subgroup.mem_iInf.2 fun w => fu_cmp_mem _ _ (hk1 _), fu_cmp_mem (s.w s.v0) k.1 (P := Kc _ n 1) hk2⟩
  refine ⟨⟨γ, hγ⟩, Φ x, Finset.mem_image_of_mem _ hx, u, ?_, (Φ k.1).2, fu_Iw _ _ (Subgroup.mem_iInf.1 hk4), ?_⟩
  · have hq : ∀ q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => Q.range ▸ Or.inr ⟨q, rfl⟩
    obtain ⟨y, ⟨hy1, hy2⟩, h1⟩ := fu_patch (fun q : Q.Q => (cmp n (Q.wq q)).comp (Ub n s).subtype)
      ((⨆ q : Q.Q, Subgroup.map (sec n s (Q.wq q)) (K.1 q)) ⊓
        ⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ V.S'), ((cmp n w).comp (Ub n s).subtype).ker)
      (fun q => cLoc (Q.wq q) k.1) fun q => by
        obtain ⟨-, h2, h3⟩ := (secU l L Ω s n hn (Q.wq q) (fu_split V _ (hq q))).2 (Q.notS q)
        have h4 := fun w => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (h3 (cLoc (Q.wq q) k.1)) w)
        exact ⟨sec n s (Q.wq q) _, ⟨Subgroup.mem_iSup_of_mem q ⟨_, hk3 q, rfl⟩, Subgroup.mem_iInf.2 fun w =>
          Subgroup.mem_iInf.2 fun hw => h4 w fun e => hw (e ▸ hq q)⟩, h2 _, fun q' hq' => h4 _ fun e => hq' (Q.inj e)⟩
    rw [← inv_mul_cancel_right u y]
    refine mul_mem (Subgroup.mem_sup_left ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => ?_,
      Subgroup.mem_iInf.2 fun q => ?_⟩) (Subgroup.mem_sup_right hy1)
    · rw [Subgroup.mem_comap, map_mul, map_inv,
        MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy2 w) hw), inv_one, mul_one]
      exact fu_cmp_mem _ _ (hk1 _)
    · rw [MonoidHom.mem_ker, map_mul, map_inv, h1 q, mul_inv_eq_one]
      exact fu_cmp (fun h => Q.notS q (Or.inl ((fu_l _).2 h))) _
  · rw [map_mul, map_mul, map_mul, hinf z hz, mul_one]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem unr_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem unr_sum {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ} {H : Type} [Group H] (t : H →* GL (Fin m) ℂ)
    (f : Fin m → M) (i : Fin m) : ∑ j : Fin m, t 1 i j • f j = f i := by
  simp [Matrix.one_apply]

theorem UpperTheory.V.Hi.partUR2Unr :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ _ hY w hw
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hF0
  have hA : F i ∈ (hset Q τ₀).X.AF ξ := hB.1 i (Set.mem_univ _)
  have h1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1 (F i) hA
  obtain ⟨ℓ, hℓ⟩ := not_forall.1 (mt h1 hi)
  refine ⟨_, hσ i ℓ, hℓ, fun x hx hk => ?_⟩
  have hne : ∀ u : Plc L, u.under (𝓞 (Lp L)) ∈ V.S' → cLoc u x = 1 := fun u hu =>
    GlobalTheory.DefU.LocRet.mem_locU_ne hx fun h => hw (h ▸ hu)
  have hS : ∀ v ∈ s.S, cLoc (s.w v) x = 1 := fun v hv => hne _ ((unr_under s v).symm ▸ V.sub hv)
  have hK : cLoc w x ∈ KO (w.adicCompletion L) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact hk
  have h2 := partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ F hB x (Subgroup.mem_inf.1 hx).1
    (fun v => hS v.1 (Or.inl v.2)) 1 (fun u => (hS u.1 (Or.inr (Or.inl u.2))).symm)
    (by
      rw [hS s.v0 (Or.inr (Or.inr rfl))]
      exact one_mem _)
    (fun u _ => by
      by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · exact UpperTheory.mem_maximalCompact_of_under_eq L n x w u h hK
      · rw [show cLoc u x = 1 from GlobalTheory.DefU.LocRet.mem_locU_ne hx h]
        exact one_mem _)
    (fun q => hne _ (Q.range.ge (Or.inr ⟨q, rfl⟩))) i ℓ
  exact (unr_sum _ (fun j => RU L n x (toForm ι e (F j) ℓ)) i).symm.trans h2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem neu_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L} {j : GLw n w →* UA L n}
    (hj : ∀ x ∈ locU n w, x = j (cLoc w x)) {g y : UA L n} (hg : cLoc w g = 1) (hy : y ∈ locU n w) : Commute g y := by
  have h1 : (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = 1 := by
    rw [hj _ (GlobalTheory.DefU.LocRet.ret w n g).2]
    have : cLoc w (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = cLoc w g := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl g
    rw [this, hg, map_one]
  have h2 := GlobalTheory.DefU.LocRet.commute_ret g ⟨y, hy⟩
  rwa [h1, inv_one, one_mul] at h2

private theorem ne_J {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {St : Type} [Fintype St] [DecidableEq St]
    {wt : St → Plc L} (hinj : Function.Injective fun u => (wt u).under (𝓞 (Lp L))) (j : ∀ u, GLw n (wt u) →* UA L n)
    (h1 : ∀ u g, j u g ∈ locU n (wt u)) (h2 : ∀ u g, cLoc (wt u) (j u g) = g) (h3 : ∀ u, ∀ x ∈ locU n (wt u), x = j u (cLoc (wt u) x)) :
    ∃ J : GV n wt →* UA L n, (∀ u g, J (Pi.mulSingle u g) = j u g) ∧ (∀ g, J g ∈ GlobalTheory.UnitaryBC.finU (E := L) (n := n)) ∧
      (∀ g u, cLoc (wt u) (J g) = g u) ∧
      (∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L))) → cLoc v (J g) = 1) ∧
      ∀ g k, (∀ u, cLoc (wt u) k = 1) → Commute k (J g) := by
  have h4 : ∀ u g (v : Plc L), v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L)) → cLoc v (j u g) = 1 := fun u g v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne (h1 u g) hv
  have hc : Pairwise fun a b => ∀ x y, Commute (j a x) (j b y) := fun a b hab x y =>
    neu_comm (h3 b) (h4 a x _ fun e => hab (hinj e).symm) (h1 b y)
  let J := MonoidHom.noncommPiCoprod j hc
  have hJ : ∀ u g, J (Pi.mulSingle u g) = j u g := fun u g => MonoidHom.noncommPiCoprod_mulSingle j u g
  have key : ∀ P : Subgroup (UA L n), (∀ u g, j u g ∈ P) → ∀ g, J g ∈ P := fun P hP g => by
    have : J.range ≤ P := by
      rw [MonoidHom.noncommPiCoprod_range]
      exact iSup_le fun u => by rintro _ ⟨g, rfl⟩; exact hP u g
    exact this ⟨g, rfl⟩
  refine ⟨J, hJ, key _ fun u g => (h1 u g).1, fun g u => ?_, fun g v hv => key (cLoc v).ker (fun u g => h4 u g v (hv u)) g,
    fun g k hk => ?_⟩
  · have : (cLoc (wt u)).comp J = Pi.evalMonoidHom (fun u => GLw n (wt u)) u := MonoidHom.pi_ext fun i x => by
      rw [MonoidHom.comp_apply, hJ, Pi.evalMonoidHom_apply]
      by_cases h : u = i
      · subst h
        rw [h2, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]
        exact h4 i x _ fun e => h (hinj e)
    exact DFunLike.congr_fun this g
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (key (Subgroup.centralizer {k}) (fun u g => Subgroup.mem_centralizer_singleton_iff.2
        (neu_comm (h3 u) (hk u) (h1 u g)).symm.eq) g)).symm

private theorem automorphic_tensor_induction_of_local_places {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n m : ℕ}
    {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
    (j : ∀ u, GLw n (wt u) →* UA L n) (J : GV n wt →* UA L n)
    (hJ : ∀ u g, J (by classical exact MonoidHom.mulSingle (fun u => GLw n (wt u)) u g) = j u g)
    (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) (hT : IsType ht τ₀ χ)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (τ : ∀ u, SmIrr (GLw n (wt u)))
    (hτ : ∀ u, IsoSum ((RU L n).comp (j u)) σ (τ u)) (F : Fin m → UA L n → ℂ) (hF0 : F ≠ 0) (hF1 : ∀ i, F i ∈ σ)
    (hF2 : ∀ (k : KT n wt) i, ∑ a, τ₀ k i a • RU L n (J k) (F a) = F i) :
    ∀ u rc, IsRec (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (τ u))) := by
  haveI : Nontrivial σ := Submodule.nontrivial_iff_ne_bot.2 hσ.ne_bot
  let ρ : Representation ℂ (GV n wt) σ :=
    (⟨σ, fun g v hv => hσ.stable (J g) v hv⟩ : Subrepresentation ((RU L n).comp J)).toRepresentation
  have hρ : ∀ g (y : σ), (ρ g y : UA L n → ℂ) = RU L n (J g) y := fun _ _ => rfl
  refine (hT.2 σ ρ τ fun u => ?_).1 ⟨fun i => ⟨F i, hF1 i⟩, fun h => hF0 (funext fun i => congrArg Subtype.val (congrFun h i)),
    fun k i => Subtype.ext ?_⟩
  · refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ _ ⊤ σ (τ u) Unit (fun _ => σ.subtype) (hτ u) (fun _ _ _ => Submodule.mem_top)
      (fun _ y _ => y.2) (fun _ g y _ => ?_) fun y _ h => Subtype.ext (h ())
    exact (hρ _ y).trans (by rw [hJ]; rfl)
  · change σ.subtype (∑ a, τ₀ k i a • ρ k ⟨F a, hF1 a⟩) = F i

    rw [map_sum, ← hF2 k i]
    rfl

theorem UpperTheory.V.Hi.partUR2Type :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, IsType (fun u : s.St => s.hw u) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ →
    ∀ τ : ∀ u : s.St, SmIrr (GLw n (s.w u)), (∀ u : s.St, IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) (τ u).ρ) → ∀ (u : s.St) rc, IsRec (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (τ u))) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ he σ hσ hY χ hT τ hτ
  letI : DecidableEq s.St := fun a b => Classical.propDecidable _
  obtain ⟨hw, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  choose j h1 h2 _ h3 using fun u : s.St => (secU l L Ω s n hn (wt s u) (hsp _ (by
    rw [hw]
    exact s.split _ (Or.inr (Or.inl u.2))))).1
  obtain ⟨J, hJ, j1, j2, j3, -⟩ := ne_J (wt := wt s)
    (fun a b hab => Subtype.ext ((hw _).symm.trans (hab.trans (hw _)))) j h1 h2 h3
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hFσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have f1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ he _ fun _ => rfl).1
  have hex : ∃ i ℓ, toForm ι e (F i) ℓ ≠ 0 := by
    by_contra h
    exact hF0 (funext fun i => f1 (F i) (hB.1 i trivial) fun ℓ => by
      by_contra h'
      exact h ⟨i, ℓ, h'⟩)
  obtain ⟨i₀, ℓ, hℓ⟩ := hex
  have j4 : ∀ g (v : Plc L), v.under (𝓞 (Lp L)) ∉ s.St → cLoc v (J g) = 1 := fun g v hv =>
    j3 g v fun a h => hv (by rw [h, hw]; exact a.2)
  refine automorphic_tensor_induction_of_local_places (fun u : s.St => s.hw u) j J (fun u g => ?_) _ χ hT hσ τ
    (fun u => UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ (j u) (h1 u) (h2 u) (h3 u) (τ u) (hτ u)) (fun i => toForm ι e (F i) ℓ)
    (fun h => hℓ (congrFun h i₀)) (fun i => hFσ i ℓ) fun k i => ?_
  · exact hJ u g
  · refine partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ he F hB (J k) (j1 _) (fun v => j4 _ _ ?_) k (fun u => (j2 _ u).symm) ?_
      (fun w hw' => ?_) (fun q => j4 _ _ fun h => Q.notS q (Or.inr (Or.inl h))) i ℓ
    · rw [hw]
      exact fun h => s.St_l _ h v.2
    · rw [j4 _ _ (by rw [hw]; exact s.v0_St)]
      exact one_mem _
    · rw [j4 _ _ fun h => hw' (V.sub (Or.inr (Or.inl h)))]
      exact one_mem _
end
