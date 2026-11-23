module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle032
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

namespace UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

section SlopeTestRemainingChoices

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori
open GlobalTheory.Parabolic (mem_fixed)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = N} {W V Z : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

private theorem isSmooth_sub (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    IsSmooth S.toRepresentation := fun y => by
  have : {g : GL (Fin N) k | S.toRepresentation g y = y} =
      {g : GL (Fin N) k | parInd (stdBlocks d hd) ρ g y.1 = y.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact isSmooth_parInd _ _ y.1

private theorem levelZeroMap_surjective {S : Subrepresentation (parInd (stdBlocks d hd) ρ)}
    {π : Representation ℂ (GL (Fin N) k) V} (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) : Function.Surjective (levelZeroMap f) := by
  intro v
  obtain ⟨u0, hu0⟩ := hf v.1
  obtain ⟨u, hu, e⟩ := IwahoriOnto.exists_fixed_map_eq (isSmooth_sub S) DepthZero.isCompact_KOne₁
    f.toLinearMap u0 fun h hh => by
      show f (S.toRepresentation h u0) = f u0
      rw [f.isIntertwining, hu0]
      exact mem_fixed.1 v.2 h hh
  exact ⟨⟨u, hu⟩, Subtype.ext (e.trans hu0)⟩

private def evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    fixed S.toRepresentation (KOne k (Fin N)) →ₗ[ℂ] W where
  toFun u := (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalOne_redK (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (κ : KO k (Fin N)) (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S (levelZero S.toRepresentation (redK k (Fin N) κ) u) =
      (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 κ := by
  show ((levelZero S.toRepresentation (redK k (Fin N) κ) u).1.1 : IndSp (stdBlocks d hd) ρ).1.1 1 = _
  rw [levelZero_apply]
  show ((parInd (stdBlocks d hd) ρ (κ : GL (Fin N) k) u.1.1 : IndSp (stdBlocks d hd) ρ)).1.1 1 = _
  rw [parInd_apply, one_mul]

private theorem val_mul_of_mem (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) (x : GL (Fin N) k) {c : GL (Fin N) k}
    (hc : c ∈ KOne k (Fin N)) :
    (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 (x * c) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 x := by
  have h : S.toRepresentation c u.1 = u.1 := mem_fixed.1 u.2 c hc
  have h2 : parInd (stdBlocks d hd) ρ c u.1.1 = u.1.1 := congrArg Subtype.val h
  exact congrArg (fun F : IndSp (stdBlocks d hd) ρ => F.1.1 x) h2

private theorem leviKOne_le_leviK {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} {d : Fin s → ℕ} :
    leviKOne k (fun a => Fin (d a)) ≤ leviK k (fun a => Fin (d a)) := by
  intro l hl
  unfold leviKOne at hl
  unfold leviK
  rw [Subgroup.mem_pi] at hl ⊢
  exact fun a ha => GlobalTheory.StepData.KOne_le_KO (hl a ha)

private theorem evalOne_mem_fixed (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S u ∈ fixed ρ (leviKOne k fun a => Fin (d a)) := by
  rw [mem_fixed]
  intro l hl
  have hpar := leviEmb_mem_parab k (stdBlocks d hd) l
  have hlaw := parInd_law (stdBlocks d hd) ρ (u.1.1 : IndSp (stdBlocks d hd) ρ) ⟨_, hpar⟩ 1
  have hK : leviEmb k (stdBlocks d hd) l ∈ KOne k (Fin N) := jLevi_le_KOne _ ⟨l, hl, rfl⟩
  have h4 := val_mul_of_mem S u 1 hK
  rw [one_mul] at h4
  simp only [mul_one, leviProj_leviEmb, deltaHalf_of_mem_leviK (leviKOne_le_leviK hl)] at hlaw
  show ρ l ((u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  rw [h4] at hlaw
  simpa using hlaw.symm

private theorem val_of_redK_mem (hPF : ParaFactor) (F : IndSp (stdBlocks d hd) ρ)
    (hF : ∀ x, ∀ c ∈ KOne k (Fin N), F.1.1 (x * c) = F.1.1 x)
    (κ₀ : KO k (Fin N)) (hκ : redK k (Fin N) κ₀ ∈ parab 𝓀[k] (stdBlocks d hd)) :
    ∃ x : leviK k fun a => Fin (d a),
      redLevi k _ x = leviProj 𝓀[k] (stdBlocks d hd) ⟨redK k (Fin N) κ₀, hκ⟩ ∧
      F.1.1 κ₀ = ρ (x : Levi k fun a => Fin (d a)) (F.1.1 1) := by
  have hg : (κ₀ : GL (Fin N) k) ∈ parahoric k (stdBlocks d hd) := (coe_mem_levelPre κ₀).2 hκ
  obtain ⟨p, x, -, hpx, hred, c, hc, hgp⟩ := (hPF k (stdBlocks d hd)).1 ⟨κ₀, hg⟩
  have h3 := parInd_law (stdBlocks d hd) ρ F p 1
  rw [mul_one, hpx, deltaHalf_of_mem_leviK x.2, Units.val_one, one_smul] at h3
  have h4 : (κ₀ : GL (Fin N) k) = p * c := hgp
  refine ⟨x, hred, ?_⟩
  rw [h4, hF _ c hc]
  exact h3



private theorem evalOne_parab (hPF : ParaFactor)
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) (h : parab 𝓀[k] (stdBlocks d hd))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    Φ (evalOne S (levelZero S.toRepresentation (h : GL (Fin N) 𝓀[k]) u)) =
      κ (leviProj 𝓀[k] (stdBlocks d hd) h) (Φ (evalOne S u)) := by
  rcases h with ⟨h, hmem⟩
  obtain ⟨κ₀, rfl⟩ := redK_surjective h
  obtain ⟨x, hx1, hx2⟩ := val_of_redK_mem hPF (u.1.1 : IndSp (stdBlocks d hd) ρ)
    (fun y c hc => val_mul_of_mem S u y hc) κ₀ hmem
  exact (congrArg Φ ((evalOne_redK S κ₀ u).trans hx2)).trans
    ((hΦ x _).trans (congrArg (fun g => κ g (Φ (evalOne S u))) hx1))

private theorem eq_zero_of_evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N)))
    (hu : ∀ γ : GL (Fin N) 𝓀[k], evalOne S (levelZero S.toRepresentation γ u) = 0) : u = 0 := by
  have hF : (u.1.1 : IndSp (stdBlocks d hd) ρ) = 0 :=
    UpperTheory.TNZ.step_indDetK k s N d hd W ρ _ 0 fun κ hκ => by
      have := hu (redK k (Fin N) ⟨κ, hκ⟩)
      rw [evalOne_redK] at this
      exact this
  exact Subtype.ext (Subtype.ext hF)

private theorem main (hPF : ParaFactor) {π : Representation ℂ (GL (Fin N) k) V}
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (hinj : ∀ w ∈ fixed ρ (leviKOne k fun a => Fin (d a)), Φ w = 0 → w = 0)
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (sec : fixed π (KOne k (Fin N)) →ₗ[ℂ] fixed S.toRepresentation (KOne k (Fin N)))
    (hs : ∀ g x, sec (levelZero π g x) = levelZero S.toRepresentation g (sec x))
    (hinv : Function.Injective sec)
    (hfix : fixed π (KOne k (Fin N)) ≠ ⊥) :
    ∃ ψ : fixed π (KOne k (Fin N)) →ₗ[ℂ] Z, ψ ≠ 0 ∧
      ∀ (p : parab 𝓀[k] (stdBlocks d hd)) (x : fixed π (KOne k (Fin N))),
        ψ (levelZero π p x) = κ (leviProj 𝓀[k] (stdBlocks d hd) p) (ψ x) := by
  obtain ⟨x0, hx0mem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  let y0 : fixed π (KOne k (Fin N)) := ⟨x0, hx0mem⟩
  have hsx : sec y0 ≠ 0 := by
    intro h0
    apply hx0
    have h1 := hinv (h0.trans (map_zero sec).symm)
    exact congrArg Subtype.val h1
  have hγ : ∃ γ, evalOne S (levelZero S.toRepresentation γ (sec y0)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hsx (eq_zero_of_evalOne S _ hc)
  obtain ⟨γ, hγ⟩ := hγ
  refine ⟨Φ ∘ₗ (evalOne S ∘ₗ sec), ?_, ?_⟩
  · intro h0
    apply hγ
    apply hinj _ (evalOne_mem_fixed S _)
    have h1 := LinearMap.congr_fun h0 (levelZero π γ y0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs] at h1
    exact h1
  · intro p x
    have h3 := evalOne_parab hPF hΦ S p (sec x)
    calc (Φ ∘ₗ (evalOne S ∘ₗ sec)) (levelZero π p x)
        = Φ (evalOne S (levelZero S.toRepresentation p (sec x))) :=
          congrArg (fun w => Φ (evalOne S w)) (hs _ _)
      _ = _ := h3

end SlopeTestRemainingChoices

end UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.Gal.InertialTypesAlt.SubquotientMaps in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.subqMap :
    FinSec → UpperTheory.Gal.TypesAndIwahori.ParaFactor → SubqMap := by
  intro hSec hPF k _ _ _ _ N s d hd W V Z _ _ _ _ _ _ ρ π κ Φ hΦ hinj hsq hfix
  obtain ⟨S, f, hf⟩ := hsq
  have : Finite (GL (Fin N) 𝓀[k]) := inferInstance
  obtain ⟨sec, hs, hfs⟩ := hSec (GL (Fin N) 𝓀[k])
    (fixed S.toRepresentation (KOne k (Fin N))) (fixed π (KOne k (Fin N)))
    (levelZero S.toRepresentation) (levelZero π) (levelZeroMap f).toLinearMap
    (fun g x => Representation.IntertwiningMap.isIntertwining _ _ (levelZeroMap f) g x) (levelZeroMap_surjective f hf)
  exact main hPF hΦ hinj S sec hs (Function.LeftInverse.injective hfs) hfix
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.Parabolic (mem_fixed)

namespace UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors

section Rep

variable {Γ X : Type} [Group Γ] [AddCommGroup X] [Module ℂ X]

private theorem idem_comm [TopologicalSpace Γ] [IsTopologicalGroup Γ] {π : Representation ℂ Γ X}
    (hπ : GlobalTheory.PRep.IsSmooth π) {H : Subgroup Γ} (hH : IsCompact (H : Set Γ)) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) (v : X) :
    idem hπ hH (π g v) = π g (idem hπ hH v) := by
  have h1 : v - idem hπ hH v ∈ twKer π H 1 := by
    rw [← idem_eq_zero_iff hπ hH, map_sub, idem_of_mem hπ hH (idem_mem hπ hH v), sub_self]
  have h3 := (idem_eq_zero_iff hπ hH).2 (twKer_le_comap π H g hg h1)
  rw [map_sub, map_sub, sub_eq_zero] at h3
  rw [h3]
  refine idem_of_mem hπ hH (mem_fixed.2 fun u hu => ?_)
  have hu' : g⁻¹ * u * g ∈ H := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) u).1 hu
    simpa using this
  have h4 : π u (π g (idem hπ hH v)) = π g (π (g⁻¹ * u * g) (idem hπ hH v)) := by
    have e1 : u * g = g * (g⁻¹ * u * g) := by group
    rw [← mul_apply_eq_comp (π u), ← map_mul, e1, map_mul, mul_apply_eq_comp]
  rw [h4, mem_fixed.1 (idem_mem hπ hH v) _ hu']

end Rep

section Tensor

variable {s : ℕ} {G V : Fin s → Type} [∀ a, Group (G a)] [∀ a, AddCommGroup (V a)] [∀ a, Module ℂ (V a)]

private noncomputable def intersection_update_fsHerm_neg_one (σ : ∀ a, Representation ℂ (G a) (V a)) (a : Fin s) :
    Representation ℂ (G a) (PiTensorProduct ℂ V) :=
  (piTensor σ).comp (MonoidHom.mulSingle G a)

private theorem position_tprod (σ : ∀ a, Representation ℂ (G a) (V a)) (a : Fin s) (g : G a) (f : ∀ b, V b) :
    intersection_update_fsHerm_neg_one σ a g (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f a (σ a g (f a))) := by
  show piTensor σ (Pi.mulSingle a g) _ = _
  rw [piTensor_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

private theorem position_smooth [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)] (σ : ∀ a, Representation ℂ (G a) (V a))
    (hσ : ∀ a, GlobalTheory.PRep.IsSmooth (σ a)) (a : Fin s) : GlobalTheory.PRep.IsSmooth (intersection_update_fsHerm_neg_one σ a) :=
  _root_.UpperTheory.Reformulated.B.SmoothTensorFactor.position_smooth σ hσ a

private noncomputable def oneMap (a : Fin s) (e : V a →ₗ[ℂ] V a) : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ V :=
  PiTensorProduct.map (Function.update (fun b => (LinearMap.id : V b →ₗ[ℂ] V b)) a e)

private theorem oneMap_tprod (a : Fin s) (e : V a →ₗ[ℂ] V a) (f : ∀ b, V b) :
    oneMap a e (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f a (e (f a))) := by
  rw [oneMap, PiTensorProduct.map_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h]

private theorem oneMap_fix [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)]
    (σ : ∀ a, Representation ℂ (G a) (V a)) (hσ : ∀ a, GlobalTheory.PRep.IsSmooth (σ a)) (a : Fin s)
    {H : Subgroup (G a)} (hH : IsCompact (H : Set (G a))) (e : V a →ₗ[ℂ] V a)
    (he : ∀ v, e v ∈ fixed (σ a) H) (hk : ∀ v, v - e v ∈ twKer (σ a) H 1)
    {w : PiTensorProduct ℂ V} (hw : w ∈ fixed (intersection_update_fsHerm_neg_one σ a) H) : oneMap a e w = w := by
  have h1 : ∀ x, oneMap a e x ∈ fixed (intersection_update_fsHerm_neg_one σ a) H := fun x => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      refine Submodule.smul_mem _ _ ?_ |> fun h => by rw [map_smul]; exact h
      rw [oneMap_tprod]
      refine mem_fixed.2 fun u hu => ?_
      rw [position_tprod, Function.update_self, mem_fixed.1 (he (f a)) u hu, Function.update_idem]
    | add x y hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  have h2 : ∀ f : ∀ b, V b, (twKer (σ a) H 1).map
      ((PiTensorProduct.tprod ℂ).toLinearMap f a) ≤ twKer (intersection_update_fsHerm_neg_one σ a) H 1 := fun f => by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, PiTensorProduct.tprod ℂ (Function.update f a v), ?_⟩
    simp [MultilinearMap.toLinearMap, position_tprod]
  have h3 : ∀ x, x - oneMap a e x ∈ twKer (intersection_update_fsHerm_neg_one σ a) H 1 := fun x => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [map_smul, ← smul_sub]
      refine Submodule.smul_mem _ _ (h2 f ⟨_, hk (f a), ?_⟩)
      rw [oneMap_tprod, map_sub]
      simp [MultilinearMap.toLinearMap]
    | add x y hx hy =>
      rw [map_add (f := _), add_sub_add_comm]; exact add_mem hx hy
  have h4 := Submodule.disjoint_def.1 (isCompl_fixed_twKer (position_smooth σ hσ a) hH).disjoint
    (w - oneMap a e w) (sub_mem hw (h1 w)) (h3 w)
  exact (sub_eq_zero.1 h4).symm

private theorem map_fix (e : ∀ a, V a →ₗ[ℂ] V a) (w : PiTensorProduct ℂ V)
    (h : ∀ a, oneMap a (e a) w = w) : PiTensorProduct.map e w = w := by
  have key : ∀ S : Finset (Fin s),
      PiTensorProduct.map (fun b => if b ∈ S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) w = w := fun S => by
    induction S using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a S ha ih =>
      have e1 : (fun b => if b ∈ insert a S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) =
          fun b => (if b ∈ S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) ∘ₗ
            Function.update (fun b => (LinearMap.id : V b →ₗ[ℂ] V b)) a (e a) b := by
        funext b
        by_cases hb : b = a
        · subst hb; simp [ha]
        · simp [hb]
      rw [e1, PiTensorProduct.map_comp, LinearMap.comp_apply]
      have := h a
      rw [oneMap] at this
      rw [this, ih]
  simpa using key Finset.univ

end Tensor

end UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors

open UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors in
theorem UpperTheory.Gal.InertialTypesAlt.tensFix :
    TensFix := by
  intro k _ _ _ _ s d V _ _ σ hσ
  have hK : ∀ a, IsCompact (KOne k (Fin (d a)) : Set (GL (Fin (d a)) k)) := fun a =>
    levelPre_bot (k := k) (n := Fin (d a)) ▸ isCompact_levelPre ⊥
  let e : ∀ a, V a →ₗ[ℂ] V a := fun a => idem (hσ a) (hK a)
  let pr : ∀ a, V a →ₗ[ℂ] fixed (σ a) (KOne k (Fin (d a))) := fun a =>
    (e a).codRestrict _ (idem_mem (hσ a) (hK a))
  refine ⟨PiTensorProduct.map pr, fun x w => ?_, fun w hw h0 => ?_⟩
  · induction w using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      simp only [map_smul, piTensor_tprod, PiTensorProduct.map_tprod]
      congr 2
      funext a
      refine Subtype.ext ?_
      rw [redLevi_apply, levelZero_apply]
      exact idem_comm (hσ a) (hK a) (KO_le_normalizer (x.2 a trivial)) (f a)
    | add x' y hx hy => simp only [map_add (f := _), hx, hy]
  · have hk : ∀ a v, v - e a v ∈ twKer (σ a) (KOne k (Fin (d a))) 1 := fun a v => by
      rw [← idem_eq_zero_iff (hσ a) (hK a), map_sub, idem_of_mem (hσ a) (hK a) (idem_mem (hσ a) (hK a) v), sub_self]
    have h1 : ∀ a, oneMap a (e a) w = w := fun a =>
      oneMap_fix σ hσ a (hK a) (e a) (idem_mem (hσ a) (hK a)) (hk a) (mem_fixed.2 fun u hu =>
        mem_fixed.1 hw (Pi.mulSingle a u) fun b _ => by
          by_cases h : b = a
          · subst h; simpa using hu
          · simpa [Pi.mulSingle_eq_of_ne h] using one_mem _)
    have h2 := map_fix e w h1
    have h3 : PiTensorProduct.map e =
        PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) ∘ₗ PiTensorProduct.map pr := by
      rw [← PiTensorProduct.map_comp]
      rfl
    rw [← h2, h3, LinearMap.comp_apply, h0, map_zero]
end
