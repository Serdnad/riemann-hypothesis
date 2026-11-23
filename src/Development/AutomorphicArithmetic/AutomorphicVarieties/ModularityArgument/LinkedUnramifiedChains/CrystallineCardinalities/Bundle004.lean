module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LiftOfBar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.RankTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.SelLow
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)}

private theorem adicCont_comp_ringHom_of_map_le {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R')
    {I : Ideal R} {J : Ideal R'} (hIJ : I.map f ≤ J) {a : Γ → R} (ha : AdicCont I a) :
    AdicCont J (fun g => f (a g)) := by
  intro N
  have h : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hIJ N
  have := (ha N).comp (Ideal.quotientMap (J ^ N) f h)
  convert this using 1
  funext g
  simp [Ideal.quotientMap_mk]

private theorem lift_pt (S : Space O F 3) (ξ : S.R →ₐ[O] O) : UpperTheory.V.Fr.IsLift O (S.ρ.map (ξ : S.R →+* O)) := by
  have hres : (res O O : O →+* ResidueField O).comp (ξ : S.R →+* O) = (res O S.R : S.R →+* ResidueField O) :=
    RingHom.ext fun x => res_map ξ x
  have hm : (maximalIdeal S.R).map (ξ : S.R →+* O) ≤ maximalIdeal O := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O O]
    have := (res_eq_zero_iff O S.R x).2 hx
    simpa [res_map] using this
  obtain ⟨hc, hb, hd⟩ := S.lift
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ?_, ?_⟩
  · exact adicCont_comp_ringHom_of_map_le _ hm (hc.1 i j)
  · exact adicCont_comp_ringHom_of_map_le _ hm (hc.2 v i)
  · rw [NRep.map_map, hres]
    exact hb
  · rw [NRep.map_map, hres]
    exact hd

private theorem box_pt {C₀ : ℕ} (hF : F.Ok C₀) (S : Space O F 3) (ξ : S.R →ₐ[O] O) :
    ∃ B : Box F 3 O, B.Of (S.ρ.map (ξ : S.R →+* O)) ∧ B.Cont (maximalIdeal O) := by
  have e : NRep.map ((ξ : S.R →+* O).comp (S.A.val : S.A →+* S.R)) S.u = S.ρ.map (ξ : S.R →+* O) := by
    apply NRep.ext
    · rfl
    · funext v i
      ext g
      rfl
  refine pr_box hF O (maximalIdeal O) _ (lift_pt S ξ).1 fun v => ?_
  rw [← e]
  exact flag hF (Or.inr rfl) S O _ v

private theorem box_unit [Algebra ℤ_[l] O] {ρ : NRep F 3 O} {B₀ : Box F 3 O} (h : B₀.Of ρ)
    (hc : B₀.Cont (maximalIdeal O)) (v : F.V) (i : Fin 2) (hu : UnitAt ρ v i) :
    ∃ B : Box F 3 O, B.Of ρ ∧ B.Cont (maximalIdeal O) ∧
      UnitStep (F.Iv v) (F.eps.comp (F.loc v)) (triOf B v) i := by
  classical
  obtain ⟨g, t, ht, hup, hdiag, hstep⟩ := hu
  have hr : ∀ s : F.Gv v, (B₀.r ((F.loc v) s)).mat = ρ.r ((F.loc0 v) s) := fun s => h.res ((F.loc0 v) s)
  let B : Box F 3 O :=
    { r := B₀.r
      nu := B₀.nu
      g := Function.update B₀.g v g
      tri := by
        intro w s
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self, hr s, ← ht s]
          exact hup s
        · rw [Function.update_of_ne hw]
          exact B₀.tri w s }
  have hBg : B.g v = g := by
    show Function.update B₀.g v g v = g
    exact Function.update_self _ _ _
  have hBw : ∀ w, w ≠ v → B.g w = B₀.g w := fun w hw => by
    show Function.update B₀.g v g w = B₀.g w
    exact Function.update_of_ne hw _ _
  have htri : triOf B v = t := by
    ext s : 1
    apply Units.ext
    show (B.g v : Matrix (Fin 3) (Fin 3) O) * (B₀.r ((F.loc v) s)).mat * ((B.g v)⁻¹ : GL (Fin 3) O) = _
    rw [hBg, hr s, ht s]
  refine ⟨B, ⟨h.atc, h.res, fun w j s => ?_⟩, hc, ?_⟩
  · by_cases hw : w = v
    · subst hw
      show ((B.g w : Matrix (Fin 3) (Fin 3) O) * ρ.r ((F.loc0 w) s) * ((B.g w)⁻¹ : GL (Fin 3) O)) j j = _
      rw [hBg, ← ht s]
      exact hdiag s j
    · show ((B.g w : Matrix (Fin 3) (Fin 3) O) * ρ.r ((F.loc0 w) s) * ((B.g w)⁻¹ : GL (Fin 3) O)) j j = _
      rw [hBw w hw]
      exact h.psi w j s
  · rw [htri]
    exact hstep

private theorem zn_ext {C₀ : ℕ} (hF : F.Ok C₀) (B : Box F 3 O) (k : ℕ) {z z' : F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)}
    (hz : z ∈ ZN B k) (hz' : z' ∈ ZN B k)
    (h : ∀ s : F.G0, z s * ((boxK B k).r s).mat = z' s * ((boxK B k).r s).mat) : z = z' := by
  have hG : ∀ s : F.G0, z s = z' s := by
    intro s
    have hu : ((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k)) = 1 :=
      Units.mul_inv _
    calc z s = z s * (((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
          rw [hu, mul_one]
      _ = z' s * (((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
          rw [← mul_assoc, h s, mul_assoc]
      _ = z' s := by rw [hu, mul_one]
  funext s
  have hc : ∀ y ∈ ZN B k, y (s * F.c) = y s := fun y hy => by
    rw [hy.1.1.2 s F.c, hy.2.1, map_zero, add_zero]
  rcases Int.units_eq_one_or (F.del s) with hs | hs
  · exact hG ⟨s, MonoidHom.mem_ker.mpr hs⟩
  · have hsc : F.del (s * F.c) = 1 := by
      rw [map_mul, hs, hF.del_c]
      rfl
    rw [← hc z hz, ← hc z' hz']
    exact hG ⟨s * F.c, MonoidHom.mem_ker.mpr hsc⟩

end

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.tan :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ cw : F.Inf → F.Γ, (∀ w, cw w * cw w = 1 ∧ F.del (cw w) = -1) → GWL { F with cw := cw } → LocE F → ∀ (S : Space O F 3) (ξ : S.R →ₐ[O] O) (v : F.V) (i : Fin 2), UnitAt (S.ρ.map (ξ : S.R →+* O)) v i → ∃ δ ∈ WDer S.ρ ξ O, ∃ δ' ∈ WDer S.ρ ξ O, LinearIndependent O ![δ, δ'] := by
  intro l _ O _ _ _ _ _ F C₀ hF hl cw hcw hGWL hL S ξ v i hu
  obtain ⟨B₀, hB₀, hc₀⟩ := box_pt hF S ξ
  obtain ⟨B, hB, hc, hstep⟩ := box_unit hB₀ hc₀ v i hu
  obtain ⟨C, hC⟩ := selLow l O F C₀ hF hl _ B (lift_pt S ξ) hB hc cw hcw hGWL hL v i hstep
  let T : Set S.R := {a | ∃ (w : F.V) (j : Fin 3) (s : F.Gv w), s ∈ F.Iv w ∧ a = ((S.ρ.ψ w j s : S.Rˣ) : S.R)}
  obtain ⟨δ, δ', hd, hdT, hd', hdT', hli⟩ := rankTwo l O S.R ξ T C hl (by
    intro k hk X hX hXf
    classical
    refine (hC k hk).2.trans (Nat.mul_le_mul_left C ?_)
    have hex : ∀ z ∈ ZN B k, ∃ δ ∈ X,
        ∀ (s : F.G0) (a b : Fin 3), δ (S.ρ.r s a b) = (z s * ((boxK B k).r s).mat) a b := by
      intro z hz
      obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := derOf l O F C₀ hF hl S ξ B hB hc k hk z hz
      refine ⟨δ, ?_, h3⟩
      rw [hX]
      refine ⟨h1, ?_⟩
      rintro a ⟨w, j, s, hs, rfl⟩
      exact h2 w j s hs
    let f : (F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)) → (S.R →ₗ[O] Ok l O k) := fun z =>
      if hz : z ∈ ZN B k then (hex z hz).choose else 0
    refine Set.ncard_le_ncard_of_injOn f (fun z hz => ?_) (fun z hz z' hz' he => ?_) hXf
    · simp only [f, dif_pos hz]
      exact (hex z hz).choose_spec.1
    · apply zn_ext hF B k hz hz'
      intro s
      ext a b
      have h1 := (hex z hz).choose_spec.2 s a b
      have h2 := (hex z' hz').choose_spec.2 s a b
      simp only [f, dif_pos hz, dif_pos hz'] at he
      rw [← h1, ← h2, he])
  exact ⟨δ, ⟨hd, fun w j s hs => hdT _ ⟨w, j, s, hs, rfl⟩⟩, δ', ⟨hd', fun w j s hs => hdT' _ ⟨w, j, s, hs, rfl⟩⟩, hli⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

section SlopeTestRemainingChoices

variable {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N]

private theorem ul_top (I : Subgroup D) (φ : D) (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (S : Subgroup D) (hS : IsClosed (S : Set D)) (hI : I ≤ S) (hφ : φ ∈ S) (s : D) : s ∈ S := by
  have := Subgroup.topologicalClosure_minimal _ (sup_le hI ((Subgroup.zpowers_le).2 hφ)) hS
  rw [h] at this
  exact this (Subgroup.mem_top s)

private theorem ul_lc (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) : IsLocallyConstant ρ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' ρ.ker, ho.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have h : ρ (g⁻¹ * x) = 1 := hx
  calc ρ x = ρ (g * (g⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = ρ g := by rw [map_mul, h, mul_one]

omit [TopologicalSpace D] [IsTopologicalGroup D] in
private theorem ul_mul (ρ : Representation ℤ D N) (s t : D) (y : N) : ρ (s * t) y = ρ s (ρ t y) := by
  rw [map_mul]; rfl

private theorem ul_zero (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) (z : D → N) (hz : z ∈ Zc ρ) (hI : ∀ s ∈ I, z s = 0)
    (hφ : z φ = 0) (s : D) : z s = 0 :=
  _root_.UpperTheory.Reformulated.B.Rb1.ul_zero ρ I φ h z hz hI hφ s

private theorem ul_ex [Finite N] (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) (I : Subgroup D) [hn : I.Normal] (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (x : N) (hx : ∀ s ∈ I, ρ s x = x) : ∃ z ∈ Zc ρ, (∀ s ∈ I, z s = 0) ∧ z φ = x := by
  have inv1 : ∀ s y, ρ s (ρ s⁻¹ y) = y := fun s y => by rw [← ul_mul, mul_inv_cancel, map_one]; rfl
  have inv2 : ∀ s y, ρ s⁻¹ (ρ s y) = y := fun s y => by rw [← ul_mul, inv_mul_cancel, map_one]; rfl
  have stab : ∀ s y, (∀ j ∈ I, ρ j y = y) → ∀ j ∈ I, ρ j (ρ s y) = ρ s y := fun s y hy j hj => by
    have h1 := hy _ (hn.conj_mem j hj s⁻¹)
    rw [inv_inv, ul_mul, ul_mul] at h1
    have h2 := congrArg (ρ s) h1
    rwa [inv1] at h2
  let T : Equiv.Perm N :=
    { toFun := fun y => x + ρ φ y
      invFun := fun y => ρ φ⁻¹ (y - x)
      left_inv := fun y => by simp only [add_sub_cancel_left, inv2]
      right_inv := fun y => by simp only [inv1, add_sub_cancel] }
  have hg : ∀ u : Subgroup.zpowers T, u ∈ Subgroup.zpowers (⟨T, Subgroup.mem_zpowers T⟩ : Subgroup.zpowers T) := by
    rintro ⟨_, k, rfl⟩
    exact ⟨k, rfl⟩
  obtain ⟨d, hd1, hd2, hd3⟩ := hd (Nat.card (Subgroup.zpowers T)) Nat.card_pos
  obtain ⟨τ, t1, t2, t3⟩ : ∃ τ : D →* Equiv.Perm N, IsLocallyConstant τ ∧ (∀ s ∈ I, τ s = 1) ∧ τ φ = T := by
    let e := (Subgroup.zpowers T).subtype.comp (zmodMulEquivOfGenerator hg rfl).toMonoidHom
    refine ⟨e.comp d, hd1.comp e, fun s hs => ?_, ?_⟩
    · rw [MonoidHom.comp_apply, hd2 s hs, map_one]
    · rw [MonoidHom.comp_apply, hd3]
      exact congrArg Subtype.val (zmodMulEquivOfGenerator_apply_ofAdd_one hg rfl)
  let S : Subgroup D :=
    { carrier := {s | ∃ a, (∀ j ∈ I, ρ j a = a) ∧ ∀ y, (∀ j ∈ I, ρ j y = y) → τ s y = a + ρ s y}
      one_mem' := ⟨0, fun j _ => map_zero _, fun y _ => by simp⟩
      mul_mem' := fun {s t} ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ =>
        ⟨a + ρ s b, fun j hj => by rw [map_add (f := _), ha j hj, stab s b hb j hj], fun y hy => by
          rw [map_mul, Equiv.Perm.mul_apply, hb' y hy,
            ha' _ (fun j hj => by rw [map_add (f := _), hb j hj, stab t y hy j hj]), map_add (f := _), ul_mul, add_assoc]⟩
      inv_mem' := fun {s} ⟨a, ha, ha'⟩ =>
        ⟨-ρ s⁻¹ a, fun j hj => by rw [map_neg, stab _ a ha j hj], fun y hy => by
          rw [map_inv, Equiv.Perm.inv_eq_iff_eq,
            ha' _ (fun j hj => by rw [map_add (f := _), map_neg, stab _ a ha j hj, stab _ y hy j hj]),
            map_add, map_neg, inv1, inv1, add_neg_cancel_left]⟩ }
  have hS : ∀ s, s ∈ S := by
    refine ul_top I φ h S ?_ (fun s hs => ⟨0, fun j _ => map_zero _, fun y hy => ?_⟩) ⟨x, hx, fun y _ => ?_⟩
    · exact isOpen_compl_iff.1 (t1.prodMk (ul_lc ρ ho)
        {p | ∃ a, (∀ j ∈ I, ρ j a = a) ∧ ∀ y, (∀ j ∈ I, ρ j y = y) → p.1 y = a + p.2 y}ᶜ)
    · rw [t2 s hs, hy s hs, zero_add]; rfl
    · rw [t3]; rfl
  refine ⟨fun s => τ s 0, ⟨t1.comp fun p => p 0, fun s t => ?_⟩, fun s hs => ?_, ?_⟩
  · obtain ⟨a, -, ha'⟩ := hS s
    obtain ⟨b, hb, hb'⟩ := hS t
    have h0 : ∀ j ∈ I, ρ j 0 = 0 := fun j _ => map_zero _
    show τ (s * t) 0 = τ s 0 + ρ s (τ t 0)
    rw [map_mul, Equiv.Perm.mul_apply, hb' 0 h0, map_zero, add_zero, ha' b hb, ha' 0 h0, map_zero, add_zero]
  · show τ s 0 = 0
    rw [t2 s hs]; rfl
  · show τ φ 0 = x
    rw [t3]
    show x + ρ φ 0 = x
    rw [map_zero, add_zero]

private theorem ul_abs [Finite N] (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) (I : Subgroup D) [I.Normal] (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) :
    ∃ Z : AddSubgroup (D → N), Finite Z ∧ (Z : Set _) ⊆ Zc ρ ∧ (∀ Y : N, (fun s => ρ s Y - Y) ∈ Z) ∧
      (∀ z ∈ Z, ∃ Y : N, ∀ s ∈ I, z s = ρ s Y - Y) ∧ Nat.card N ≤ Nat.card Z := by
  have hsub : ∀ {a b : D → N}, a ∈ Zc ρ → b ∈ Zc ρ → a - b ∈ Zc ρ := fun {a b} ha hb =>
    ⟨ha.1.sub hb.1, fun s t => by
      simp only [Pi.sub_apply, ha.2 s t, hb.2 s t, map_sub]; abel⟩
  have h0 : (0 : D → N) ∈ Zc ρ := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  let Z : AddSubgroup (D → N) := AddSubgroup.ofSub {z | z ∈ Zc ρ ∧ ∃ Y : N, ∀ s ∈ I, z s = ρ s Y - Y}
    ⟨0, h0, 0, fun s _ => by simp⟩
    (fun a ⟨ha, Y, hY⟩ b ⟨hb, Y', hY'⟩ => by
      rw [← sub_eq_add_neg]
      refine ⟨hsub ha hb, Y - Y', fun s hs => ?_⟩
      rw [Pi.sub_apply, hY s hs, hY' s hs, map_sub]; abel)
  have hcob : ∀ Y : N, (fun s => ρ s Y - Y) ∈ Z := fun Y =>
    ⟨⟨(ul_lc ρ ho).comp fun p => p Y - Y, fun s t => by
      simp only [ul_mul, map_sub]; abel⟩, Y, fun _ _ => rfl⟩
  have hfin : Finite Z := by
    refine Finite.of_injective (fun z : Z => (z.2.2.choose, z.1 φ)) fun a b hab => Subtype.ext ?_
    obtain ⟨e1, e2⟩ := Prod.ext_iff.1 hab
    refine sub_eq_zero.1 (funext (ul_zero ρ I φ h _ (hsub a.2.1 b.2.1) (fun s hs => ?_) (sub_eq_zero.2 e2)))
    have e1' : a.2.2.choose = b.2.2.choose := e1
    rw [Pi.sub_apply, a.2.2.choose_spec s hs, b.2.2.choose_spec s hs, e1', sub_self]
  refine ⟨Z, hfin, fun z hz => hz.1, hcob, fun z hz => hz.2, ?_⟩
  let r : Z →+ (I → N) := AddMonoidHom.mk' (fun z s => z.1 s.1) fun _ _ => rfl
  let π : N →+ (I → N) := AddMonoidHom.mk' (fun Y s => ρ s.1 Y - Y) fun a b => funext fun s => by
    simp only [map_add (f := _), Pi.add_apply]; abel
  have hr : r.range = π.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨Y, hY⟩ := z.2.2
      exact ⟨Y, funext fun s => (hY s.1 s.2).symm⟩
    · rintro _ ⟨Y, rfl⟩
      exact ⟨⟨_, hcob Y⟩, rfl⟩
  have hk : Nat.card π.ker ≤ Nat.card r.ker := by
    have hex : ∀ x : π.ker, ∃ z : r.ker, z.1.1 φ = x.1 := fun x => by
      obtain ⟨z, z1, z2, z3⟩ := ul_ex ρ ho I φ h hd x.1 fun s hs => sub_eq_zero.1 (congrFun x.2 ⟨s, hs⟩)
      exact ⟨⟨⟨z, z1, 0, fun s hs => by rw [z2 s hs]; simp⟩, funext fun s => z2 s.1 s.2⟩, z3⟩
    choose f hf using hex
    exact Nat.card_le_card_of_injective f fun a b hab => Subtype.ext (by rw [← hf a, ← hf b, hab])
  rw [← π.ker.card_mul_index, ← r.ker.card_mul_index, AddSubgroup.index_ker, AddSubgroup.index_ker, hr]
  exact Nat.mul_le_mul_right _ hk

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.J.unrLow :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), IsPlaceOver A v → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ (Dec (F := F) A) N), IsOpen (ρ.ker : Set (Dec (F := F) A)) → ∃ Z : AddSubgroup (Dec (F := F) A → N), Finite Z ∧ (Z : Set _) ⊆ Zc ρ ∧ (∀ Y : N, (fun s => ρ s Y - Y) ∈ Z) ∧ (∀ z ∈ Z, ∃ Y : N, ∀ s : Dec (F := F) A, s.1 ∈ Ine (F := F) A → z s = ρ s Y - Y) ∧ Nat.card N ≤ Nat.card Z := by
  intro F Ω _ _ _ _ _ A v hA N _ _ ρ ho
  obtain ⟨φ, -, h1, h2⟩ := GC.decZhat F Ω v A hA
  haveI : ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).Normal := ⟨fun n hn g => conj_mem_Ine g.2 hn⟩
  exact ul_abs ρ ho _ φ h1 h2
end
