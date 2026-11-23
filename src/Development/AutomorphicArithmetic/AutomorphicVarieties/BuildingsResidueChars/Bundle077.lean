module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle048
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AutTranslate
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle076
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S] [Module ℂ S]

private def eqForms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add (f := _)]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

private noncomputable def eqRep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU (E := E) (n := n)) (eqForms ρ) where
  toFun k := (LinearMap.llcomp ℂ _ _ _ (RU E n k)).restrict (p := eqForms ρ) (q := eqForms ρ) fun f h =>
    ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
      change RU E n k (f (ρ x v)) = RU E n x (RU E n k (f v))
      rw [h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g => congrArg (f.1 v) (mul_one g))
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g =>
    congrArg (f.1 v) (mul_assoc g a b).symm)

private theorem eqRep_adm [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (f : eqForms ρ) :
    ∃ K : Subgroup (finU (E := E) (n := n)), (∀ k ∈ K, eqRep ρ k f = f) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed (eqRep ρ) K) ∧
      ∀ w, (Set.range fun k : K => eqRep ρ k w).Finite :=
  _root_.UpperTheory.Reformulated.B.Gr38.eqRep_adm ρ f

end

theorem UpperTheory.admissible_equivariantForms_representation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∀ v, f v ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdefB hinv S _ _ _ ρ hsp f hfa hfe v
  classical
  by_cases hv : v = 0
  · rw [hv, map_zero]
    exact zero_mem _
  let ev : eqForms ρ →ₗ[ℂ] (UA E n → ℂ) := LinearMap.applyₗ v ∘ₗ (eqForms ρ).subtype
  let B' : eqForms ρ →ₗ⋆[ℂ] eqForms ρ →ₗ[ℂ] ℂ := (B.compl₂ ev).comp ev
  have hB' : ∀ u w, B' u w = B (u.1 v) (w.1 v) := fun _ _ => rfl
  have hev : ∀ u : eqForms ρ, u.1 v = 0 → u = 0 := fun u hu => by
    have h1 : ∀ T ∈ Submodule.span ℂ (Set.range ρ), u.1 (T v) = 0 := by
      intro T hT
      induction hT using Submodule.span_induction with
      | mem T hT =>
        obtain ⟨x, rfl⟩ := hT
        rw [u.2.2, hu, map_zero]
      | zero => simp
      | add a b _ _ ha hb => rw [LinearMap.add_apply, map_add (f := _), ha, hb, add_zero]
      | smul c a _ ha => rw [LinearMap.smul_apply, map_smul, ha, smul_zero]
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    have h2 := h1 (LinearMap.smulRight l w) (hsp ▸ Submodule.mem_top)
    rw [LinearMap.smulRight_apply, hl, one_smul] at h2
    exact h2
  have hdef : ∀ u, B' u u = 0 → u = 0 := fun u hu => hev u (hdefB _ (u.2.1 v) hu)
  have hinv' : ∀ g u w, B' (eqRep ρ g u) (eqRep ρ g w) = B' u w := fun g u w =>
    hinv g _ _ (u.2.1 _) (w.2.1 _)
  have hmem := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (finU (E := E) (n := n)) (eqForms ρ) (eqRep ρ) B' hdef hinv' (eqRep_adm ρ) ⟨f, hfa, hfe⟩
  refine (iSup_le ?_ : _ ≤ (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap ev) hmem
  rintro ⟨U, hU0, hU, hirr⟩
  let j : U →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := (eqForms ρ).subtype ∘ₗ U.subtype
  have hj : ∀ (p : U) (x : infU E n) v, j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => p.1.2.2 x v
  have hrep : IsAutRepU (Pairs.img j) := by
    refine ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun h => hU0 ?_, fun N hle hN => ?_⟩
    · have h1 : Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact p.1.2.1 v)
      exact h1 hφ
    · refine Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          change RU E n a.1 _ ∈ Pairs.img j
          rw [← hj]
          exact Pairs.apply_mem_img _ _ _)
        exact fun φ hφ => h1 hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          exact Pairs.apply_mem_img j ⟨eqRep ρ k p.1, hU k _ p.2⟩ v)
        exact fun φ hφ => h1 hφ
    · rw [Submodule.eq_bot_iff]
      intro u hu
      have := Pairs.apply_mem_img j ⟨u, hu⟩ v
      rw [h, Submodule.mem_bot] at this
      exact hev u this
    · refine Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
        (Q := fun k : finU (E := E) (n := n) => (eqRep ρ k).restrict (hU k)) (T := fun k => RU E n k.1) (fun _ _ _ => rfl)
        (fun P hP => ?_) hle (fun x => hN x.1) (fun k => hN k.1)
      rcases hirr (P.map U.subtype) (Submodule.map_subtype_le U P) (by
        rintro g _ ⟨p, hp, rfl⟩
        exact ⟨_, hP g p hp, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_bot _).symm)
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_subtype_top _).symm)
  intro u hu
  exact le_iSup (fun σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ} => σ.1) ⟨_, hrep⟩
    (Pairs.apply_mem_img j ⟨u, hu⟩ v)
end

section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem fac_mul (c c' : ℂ) (t t' q : ℝ) (P P' : ℂ[X]) (s : ℂ) :
    fac c t q P s * fac c' t' q P' s = fac (c * c') (t + t') q (P * P') s := by
  simp only [fac, eval_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [div_mul_div_comm]
  congr 1
  ring

private theorem fac_one (c : ℂ) (t q q' : ℝ) (s : ℂ) : fac c t q 1 s = fac c t q' 1 s := by
  simp only [fac, eval_one]

private def IsFac (f : ℂ → ℂ) (q : ℝ) (P : ℂ[X]) : Prop := ∃ (c : ℂ) (t : ℝ), ∀ s : ℂ, f s = fac c t q P s

private theorem IsFac.mul {f g : ℂ → ℂ} {q : ℝ} {P Q : ℂ[X]} (hf : IsFac f q P) (hg : IsFac g q Q) :
    IsFac (fun s => f s * g s) q (P * Q) := by
  obtain ⟨c, t, h⟩ := hf
  obtain ⟨c', t', h'⟩ := hg
  exact ⟨c * c', t + t', fun s => by rw [← fac_mul, ← h, ← h']⟩

private theorem IsFac.one {f : ℂ → ℂ} {q : ℝ} (q' : ℝ) (hf : IsFac f q 1) : IsFac f q' 1 := by
  obtain ⟨c, t, h⟩ := hf
  exact ⟨c, t, fun s => (h s).trans (fac_one c t q q' s)⟩

private theorem isFac_prod_one {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (q : ℝ) (h : ∀ u ∈ S, IsFac (f u) q 1) :
    IsFac (fun s => ∏ u ∈ S, f u s) q 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 0, fun s => by simp [fac]⟩
  | insert a S ha ih =>
    have h1 := (h a (Finset.mem_insert_self _ _)).mul (ih fun u hu => h u (Finset.mem_insert_of_mem hu))
    rw [mul_one] at h1
    simpa only [Finset.prod_insert ha] using h1

private theorem isFac_prod {ι : Type} (S : Finset ι) (v : ι) (hv : v ∈ S) (f : ι → ℂ → ℂ) (q : ℝ) (P : ℂ[X])
    (h0 : IsFac (f v) q P) (h : ∀ u ∈ S, u ≠ v → IsFac (f u) q 1) : IsFac (fun s => ∏ u ∈ S, f u s) q P := by
  have h1 := h0.mul (isFac_prod_one (S.erase v) f q fun u hu => h u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu))
  rw [mul_one] at h1
  obtain ⟨c, t, h1⟩ := h1
  exact ⟨c, t, fun s => by rw [← h1 s]; exact (Finset.mul_prod_erase S (fun u => f u s) hv).symm⟩

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem unit_mul {ν c : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) (h' : Ad3.IsUnit1 c) : Ad3.IsUnit1 (ν * c) :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h.2, h'.2, mul_one]⟩

private theorem unit_inv {ν : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) : Ad3.IsUnit1 ν⁻¹ :=
  ⟨h.1.inv, fun x => by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h.2, inv_one]⟩

private theorem lin_ne {ν : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) (x : ℂ) (hx : 1 < ‖x‖) : (lin ν).eval x ≠ 0 := by
  unfold lin
  split_ifs
  · simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
    intro h0
    have h1 := congrArg norm (sub_eq_zero.1 h0)
    rw [norm_one, norm_mul, h.2, one_mul] at h1
    linarith
  · simp

private theorem local_linear_factor_ramified {ν c : Fˣ →* ℂˣ} (h : Ram3 ν c) : lin3 ν c = 1 := by
  simp only [lin3, lin, if_neg h.1, if_neg h.2.1, if_neg h.2.2, mul_one]

private theorem gamma_factor_rank_three_form [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) {ν c : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν)
    (h' : Ad3.IsUnit1 c) : IsFac (Ad3.gam3 ψ ν c) (residueCard F : ℝ) (lin3 ν c) :=
  IsFac.mul (f := fun s => Ad3.gam ψ (ν * c) s * Ad3.gam ψ c s)
    (IsFac.mul (UpperTheory.local_gamma_factor_exponential_form F ψ _ (unit_mul h h').1) (UpperTheory.local_gamma_factor_exponential_form F ψ _ h'.1))
    (UpperTheory.local_gamma_factor_exponential_form F ψ _ (unit_mul (unit_inv h) h').1)

end Loc

private theorem loc_unit (c : HeckeCharacter ℚ) (v : Ad3.Pl) : Ad3.IsUnit1 (localChar c v) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c v, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar, Circle.norm_coe]⟩

private theorem loc_fac (D : Ad3.Dat) (c : HeckeCharacter ℚ) (v : Ad3.Pl) :
    IsFac (Ad3.gam3 (localAdelicChar ℚ v) (D.ν v) (localChar c v)) (Ideal.absNorm v.asIdeal : ℝ) (lin3 (D.ν v) (localChar c v)) := by
  have h := gamma_factor_rank_three_form (localAdelicChar ℚ v) (D.unit v) (loc_unit c v)
  rwa [residueCard_adicCompletion] at h

private theorem fin_fac (D : Ad3.Dat) (c : HeckeCharacter ℚ) (S : Finset Ad3.Pl) (v : Ad3.Pl) (hv : v ∈ S)
    (h : ∀ u ∈ S, u ≠ v → Ram3 (D.ν u) (localChar c u)) :
    IsFac (fun s => ∏ u ∈ S, Ad3.gam3 (localAdelicChar ℚ u) (D.ν u) (localChar c u) s) (Ideal.absNorm v.asIdeal : ℝ)
      (lin3 (D.ν v) (localChar c v)) :=
  isFac_prod S v hv (fun u => Ad3.gam3 (localAdelicChar ℚ u) (D.ν u) (localChar c u)) _ _ (loc_fac D c v) fun u hu huv => by
    have h1 := loc_fac D c u
    rw [local_linear_factor_ramified (h u hu huv)] at h1
    exact h1.one _
end
