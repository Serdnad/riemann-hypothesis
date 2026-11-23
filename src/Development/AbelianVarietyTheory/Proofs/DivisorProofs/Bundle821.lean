module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Mathlib.RepresentationTheory.Invariants
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle790
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOneFormsIsBaseChangeTangentRep
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Mathlib.RingTheory.Invariant.Defs
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

noncomputable section

namespace GlobalTheory.GenericProduct

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne NumberField Module

def OneGenericVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 →
    ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
      (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1

section Twist

variable {K P V : Type} [Field K] [Group P] [AddCommGroup V] [Module K V]

def twistInv (τ : Representation K P V) (c : P →* Kˣ) : Representation K P V where
  toFun h := (((c h)⁻¹ : Kˣ) : K) • τ h
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

theorem twistInv_apply (τ : Representation K P V) (c : P →* Kˣ) (h : P) :
    twistInv τ c h = (((c h)⁻¹ : Kˣ) : K) • τ h := rfl

theorem sum_trace_mul_inv [Fintype P] [CharZero K] [FiniteDimensional K V] (τ : Representation K P V) (c : P →* Kˣ) :
    ∑ h : P, LinearMap.trace K V (τ h) * (((c h)⁻¹ : Kˣ) : K) =
      (Nat.card P : K) * (finrank K (twistInv τ c).invariants : K) := by
  have hc : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI : Invertible (Nat.card P : K) := invertibleOfNonzero hc
  letI : Invertible (Fintype.card P : K) := invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact hc)
  have h := Representation.card_inv_mul_sum_char_eq_finrank (twistInv τ c)
  rw [← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.character, twistInv_apply, map_smul, smul_eq_mul, mul_comm]

end Twist

theorem sum_unip_eq {F : Type} [Field F] {r : ℕ} [Fintype (unip F r)] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) :
    ∑ h : unip F r, LinearMap.trace ℂ V (τ h) * (((addCharHom ψ (supHom F r) h)⁻¹ : ℂˣ) : ℂ) =
      (Nat.card (unip F r) : ℂ) * (whDim ψ τ : ℂ) := by
  have h := sum_trace_mul_inv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))
  have e : (twistInv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))).invariants =
      eig τ (unip F r : Set (GL (Fin r) F)) fun g => ψ (edgeSum supEdge g) := by
    ext v
    simp only [Representation.mem_invariants, eig, Submodule.mem_iInf, LinearMap.mem_ker, twistInv_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have key : ∀ g : unip F r, ((((addCharHom ψ (supHom F r) g)⁻¹ : ℂˣ) : ℂ) • (τ.comp (unip F r).subtype g) v = v ↔
        τ g v = ψ (edgeSum supEdge (g : GL (Fin r) F)) • v) := by
      intro g
      have hv : ψ (edgeSum supEdge (g : GL (Fin r) F)) = ((addCharHom ψ (supHom F r) g : ℂˣ) : ℂ) := rfl
      rw [hv, Units.val_inv_eq_inv_val, inv_smul_eq_iff₀ (Units.ne_zero _)]
      rfl
    exact ⟨fun H g hg => (key ⟨g, hg⟩).1 (H ⟨g, hg⟩), fun H g => (key g).2 (H g.1 g.2)⟩
  rw [e] at h
  exact h

def piEquiv {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H) ≃ ∀ i, H i where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

attribute [local instance] resField finite_res

theorem genericMultOne (hL : OneGenericVector) : GenericMultOne := by
  classical
  intro E _ _ Pg r K _ _ s ψ hψ χ hχ
  obtain ⟨b, V, i1, i2, i3, σ, hσ, hs⟩ := hχ
  letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _
  letI : ∀ PP : ↥Pg, Fintype (unip (kP PP.1) r) := fun PP => Fintype.ofFinite _
  apply s.injective
  let ψ' : ∀ PP : ↥Pg, AddChar (kP PP.1) ℂ := fun PP => s.toMonoidHom.compAddChar (ψ PP.1)
  have hψ' : ∀ PP : ↥Pg, ψ' PP ≠ 1 := by
    intro PP h
    refine hψ PP.1 PP.2 ?_
    ext x
    apply s.injective
    have := DFunLike.congr_fun h x
    simpa [ψ'] using this
  let e : (P0 Pg r ψ).H ≃ ∀ PP : ↥Pg, unip (kP PP.1) r := piEquiv fun PP : ↥Pg => unip (kP PP.1) r
  let f : ∀ PP : ↥Pg, unip (kP PP.1) r → ℂ := fun PP h =>
    LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) h) *
      (((addCharHom (ψ' PP) (supHom (kP PP.1) r) h)⁻¹ : ℂˣ) : ℂ)
  have hf : ∀ PP : ↥Pg, ∑ h, f PP h = (Nat.card (unip (kP PP.1) r) : ℂ) := by
    intro PP
    letI : Fintype (kP PP.1) := Fintype.ofFinite _
    haveI := finite_parInd (b PP) (σ PP)
    have h1 := sum_unip_eq (ψ' PP) (parInd (F := kP PP.1) (b PP) (σ PP))
    rw [hL (kP PP.1) (ψ' PP) (hψ' PP) r (V PP) (b PP) (σ PP) (hσ PP), Nat.cast_one, mul_one] at h1
    exact h1
  have hterm : ∀ h : (P0 Pg r ψ).H, s (χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K)) = ∏ PP, f PP (e h PP) := by
    intro h
    have hchi : (P0 Pg r ψ).chi h = ∏ PP : ↥Pg, addCharHom (ψ PP.1) (supHom (kP PP.1) r) (e h PP) := by
      exact MonoidHom.finsetProd_apply (fun PP : ↥Pg => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp
        (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) Finset.univ h
    rw [map_mul, hs, hchi, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_prod, map_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [f, Units.val_inv_eq_inv_val]
    rfl

  rw [map_sum, Finset.sum_congr rfl fun h _ => hterm h, map_natCast, Nat.card_congr e, Nat.card_pi, Nat.cast_prod,
  ← Finset.prod_congr rfl fun PP _ => hf PP, Fintype.prod_sum]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.GenericProduct
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.finsum_semidirect_coset_pairing_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_pair_ne_zero) | (exact GlobalTheory.Shin.finsum_coset_pair_ne_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_pair_ne_zero <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory.ZJ

theorem exists_algEquiv_lift_residue (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l))
    (φ : kb l ≃+* kb l)
    (hφ : ∀ x : OO l, (x : PadicAlgCl l) ∈ L → φ (residue (OO l) x) = residue (OO l) x) :
    ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : OO l,
      residue (OO l) y = φ (residue (OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  classical
  haveI : IsAlgClosure L (PadicAlgCl l) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L⟩
  haveI : IsGalois L (PadicAlgCl l) := {}
  have hmem : ∀ (g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l) {x : PadicAlgCl l}, x ∈ OO l → g x ∈ OO l :=
    fun g _ hx => algEquiv_mem_OO (g.restrictScalars ℚ_[l]) hx
  letI : MulSemiringAction (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (OO l) :=
    { smul := fun g x => ⟨g x, hmem g x.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl
      smul_zero := fun g => Subtype.ext (map_zero g)
      smul_add := fun g _ _ => Subtype.ext (map_add g _ _)
      smul_one := fun g => Subtype.ext (map_one g)
      smul_mul := fun g _ _ => Subtype.ext (map_mul g _ _) }
  have hsmul : ∀ (g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (x : OO l),
      ((g • x : OO l) : PadicAlgCl l) = g x := fun _ _ => rfl
  let A : Subring (OO l) := L.toSubalgebra.toSubring.comap (OO l).subtype
  have hA : ∀ a : A, (((a : OO l) : PadicAlgCl l)) ∈ L := fun a => a.2
  haveI : SMulCommClass (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) A (OO l) := ⟨fun g a b => by
    apply Subtype.ext
    change g (((a : OO l) : PadicAlgCl l) * b) = ((a : OO l) : PadicAlgCl l) * g b
    rw [map_mul]
    congr 1
    exact g.commutes (⟨_, hA a⟩ : L)⟩
  letI : TopologicalSpace (OO l) := ⊥
  haveI : DiscreteTopology (OO l) := ⟨rfl⟩
  haveI : ContinuousSMul (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (OO l) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := L) (x : PadicAlgCl l)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  haveI : Algebra.IsInvariant A (OO l) (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (b : PadicAlgCl l)).2
      fun g => congrArg Subtype.val (hb g)
    have hbL : (b : PadicAlgCl l) ∈ L := hk ▸ k.2
    exact ⟨⟨b, hbL⟩, rfl⟩
  set Q := maximalIdeal (OO l) with hQ
  let φ' : ((OO l) ⧸ Q) ≃ₐ[A ⧸ Q.under A] ((OO l) ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := (φ : ((OO l) ⧸ Q) ≃+* ((OO l) ⧸ Q))) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hφ (a : OO l) (hA a))
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (Q.under A) Q φ'
  refine ⟨σ, fun x y hxy => ?_⟩
  have h1 : Ideal.Quotient.mk Q (σ • x) = φ (residue (OO l) x) :=
    DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)
  have h2 : residue (OO l) (σ • x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_eq_zero.2 h1
  have h3 : ¬ IsUnit (σ • x - y) := by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h2
    exact h2
  have h4 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 h3
  simpa [hsmul] using h4

end GlobalTheory.ZJ
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.ZH.PerpKerRank

theorem exists_eStd_eq_addHom (g n : ℕ) (φ : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n) :
    ∃ a, ∀ b, eStd g n a b = φ b := by
  obtain ⟨a, ha⟩ := (eStdBilin_bijective (g := g) (n := n)).2 (φ.toZModLinearMap n)
  exact ⟨a, fun b => LinearMap.congr_fun ha b⟩

theorem nonempty_perp_ker_equiv_hom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {X : Type} [AddCommGroup X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy) :
    Nonempty (S.perp yy.ker ≃+ (X →+ ZMod (S.r * S.N))) := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ (t : S.perp yy.ker) (b b' : S.Gam), yy b = yy b' → eStd S.g _ t b = eStd S.g _ t b' := by
    intro t b b' e
    have h0 : eStd S.g _ t (b - b') = 0 := t.2 _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  let Λ : S.perp yy.ker →+ X →+ ZMod (S.r * S.N) := AddMonoidHom.mk'
    (fun t => AddMonoidHom.mk' (fun α => eStd S.g _ t (σ α)) fun α β => by
      rw [← eStd_add_right]
      exact ind t _ _ (by rw [map_add (f := _), hσ, hσ, hσ, QuotientAddGroup.mk_add]))
    fun t t' => AddMonoidHom.ext fun α => eStd_add_left _ _ _
  have hΛ : ∀ (t : S.perp yy.ker) b α, yy b = QuotientAddGroup.mk α → Λ t α = eStd S.g _ t b :=
    fun t b α e => ind t _ _ ((hσ α).trans e.symm)
  refine ⟨AddEquiv.ofBijective Λ ⟨(injective_iff_map_eq_zero _).2 fun t ht =>
    Subtype.ext (eq_zero_of_eStd_eq_zero fun b => ?_), fun l => ?_⟩⟩
  · obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy b)
    rw [← hΛ t b α e.symm, ht, AddMonoidHom.zero_apply]
  · let l' : (X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) →+ ZMod (S.r * S.N) :=
      QuotientAddGroup.lift _ l (by
        rintro _ ⟨x, rfl⟩
        show l ((S.r * S.N) • x) = 0
        rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul])
    obtain ⟨a, ha⟩ := exists_eStd_eq_addHom S.g _ (l'.comp yy)
    refine ⟨⟨a, fun h hh => (ha h).trans ?_⟩, AddMonoidHom.ext fun α => (ha (σ α)).trans ?_⟩
    · rw [AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 hh, map_zero]
    · rw [AddMonoidHom.comp_apply, hσ]
      rfl

theorem perp_ker_equiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range), Function.Surjective yy → S.IsoFree (S.perp yy.ker) → Nonempty (S.perp yy.ker ≃+ (Fin (Module.finrank ℤ X) → ZMod (S.r * S.N))) := by
  intro o Ω _ _ _ S X _ _ _ yy hs _
  obtain ⟨e⟩ := nonempty_perp_ker_equiv_hom S yy hs
  exact ⟨e.trans
    ((addMonoidHomLequivInt ℤ).toAddEquiv.trans ((Module.finBasis ℤ X).constr ℤ).symm.toAddEquiv)⟩

end GlobalTheory.ZH.PerpKerRank
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifTorsK

def PsiNormAt (p : ℕ) [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [Algebra (FractionRing V) (PadicAlgCl p)]
    (D : DegPre V) (χ : D.X) (r : ℝ) : Prop :=
  ∀ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) →
    ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi χ).s j).val)‖ = r

theorem psiNorm_iff {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (χ : u.D.toPre.X) (r : ℝ) :
    u.PsiNorm χ r ↔ PsiNormAt p u.D.toPre χ r := Iff.rfl

end GlobalTheory.UnifTorsK
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.ZH

namespace GlobalTheory.UPoinc.USum

def IsTwVal {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A}
    (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀)
    (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]))
    (U : ThetaGrp P.A P.L N T), α.IsGen ∧ SymLift P.A P.L N N x U ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      gs r z ⊤ v * (val α (r ≫ (ptSecT P.A h).left) z J * val τ (r ≫ β.left) z J).val =
        (GlobalTheory.CommPairing.tval U (r ≫ (ptSecT P.A h).left) z J * val α (r ≫ (ptSecT P.A (x * h)).left) z J).val *
          sval (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => 1) θ
            (r ≫ (ptSecT P.A ((x * h) ^ m)).left ≫ (β ▷ P.A).left) z J

def wtChar {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (a : S.Gam) :
    T →+ ZMod S.N where
  toFun t := ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) a)
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add (f := _)]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

abbrev genPt {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) : Over (Sp R) := Over.mk (spMap ψ)

def genTo {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) : genPt ψ ⟶ baseOver (Sp R) :=
  Over.homMk (spMap ψ) (Category.comp_id _)

def IsGenLab {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω')
    (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left)
    (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)) : Prop :=
  IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    (∀ b, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = (x b).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt b).left) ∧
    ∀ k, x (lab k) = genTo _ ≫ ρ.pt k

end GlobalTheory.UPoinc.USum
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

theorem _root_.GlobalTheory.T.qExpansionValuationBound_ring_closure : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (N : ℕ), 0 < N → (∀ (r : ℝ) (c : ℂ), Sz l lam r c → QAll (Sz l lam r) N fun _ => c) ∧ (∀ (r s : ℝ) f, r ≤ s → QAll (Sz l lam r) N f → QAll (Sz l lam s) N f) ∧ (∀ (r : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam r) N g → (QAll (Sz l lam r) N fun τ => f τ + g τ) ∧ QAll (Sz l lam r) N fun τ => f τ - g τ) ∧ (∀ (r s : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam s) N g → QAll (Sz l lam (r + s)) N fun τ => f τ * g τ) ∧ (∀ (r : ℝ) f (k : ℕ), QAll (Sz l lam r) N f → QAll (Sz l lam (k * r)) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam r) N (f k)) → QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ) ∧ (∀ (κ : Type) (t : Finset κ) (r : κ → ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) → QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ) := by
  first | exact @GlobalTheory.QFam.QSz.qAll_sz_ring | exact GlobalTheory.QFam.QSz.qAll_sz_ring | (intros; apply GlobalTheory.QFam.QSz.qAll_sz_ring <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_global_oneForms_isBaseChange_tangentRep : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∀ (W : Type) [AddCommGroup W] [Module R W], TanRep A W → ∃ j : W →ₗ[R] GlobForm A.hom, ∀ T : AffOp A.left, ∃ e : W →ₗ[R] Ω[(OAff A.hom).obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange ((OAff A.hom).obj T) e := by
  first | exact @GlobalTheory.TanForms.exists_globForm_isBaseChange | exact GlobalTheory.TanForms.exists_globForm_isBaseChange | (intros; apply GlobalTheory.TanForms.exists_globForm_isBaseChange <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_cech_conerve_quasiIso : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  intro R _ T _ _ Ψ hΨ U V g hg
  obtain ⟨e, he, hc⟩ := GlobalTheory.T.cechConerve_map_eq_cechNerve_of_preservesWidePushouts T Ψ hΨ U V g
  have h2 := GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' R _ _ (Ψ.map g).unop hg
  let h : ((Arrow.mk (Ψ.map g).unop).cechNerve : Spc) ⟶ disc.obj (Ψ.obj U).unop :=
    (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom
  have key : lev Ψ (coAug g) = e ≫ h := hc.symm
  have h2' : QuasiIso ((chains R).map h) := h2
  rw [key, Functor.map_comp]
  haveI : IsIso ((chains R).map e) := inferInstance
  exact quasiIso_comp _ _
end GlobalTheory.EtC
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.isSSec_glueSectionByPartition_of_holo : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → A.IsSSec (A.kap + la) (glue C la u) := by
  first | exact @GlobalTheory.OTY.glue_isSSec_of_holo | exact GlobalTheory.OTY.glue_isSSec_of_holo | (intros; apply GlobalTheory.OTY.glue_isSSec_of_holo <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.peak_section_small_first_jet_normal_frame : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  first | exact @GlobalTheory.JetSmall.main | exact GlobalTheory.JetSmall.main | (intros; apply GlobalTheory.JetSmall.main <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom → ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S) (g : Over.mk s ⟶ U), IsStalk O s ∧ ∃ v, g.left v = u := by
  first | (exact @GlobalTheory.EtC.exists_isStalk_over_point) | (exact GlobalTheory.EtC.exists_isStalk_over_point) | (intros; apply GlobalTheory.EtC.exists_isStalk_over_point  <;> assumption)
end
