module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Invariants
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
public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology groupHomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def TateAcyclic (M : Rep.{u} k G) : Prop := ∀ n : ℤ, IsZero (tateCohomology M n)

theorem TateAcyclic.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : TateAcyclic N) : TateAcyclic M := fun n => by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 ((tateCohomologyFunctor n).obj M) = 0
  rw [← (tateCohomologyFunctor n).map_id, ← h, Functor.map_comp,
    (hN n).eq_of_tgt ((tateCohomologyFunctor n).map i) 0, zero_comp]

theorem TateAcyclic.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : TateAcyclic N) :
    TateAcyclic M :=
  hN.of_retract e.hom e.inv e.hom_inv_id

theorem isZero_tateCohomology_zero_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, (∀ g : G, M.ρ g m = m) → ∃ y : M, M.ρ.norm y = m) :
    IsZero (tateCohomology M 0) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousCochains M).X 0, (inhomogeneousCochains M).d 0 1 x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 0, M.tateNorm x₁ = x₂
  intro x₂ hd
  have hinv : ∀ g : G, M.ρ g ((cochainsIso₀ M).hom x₂) = (cochainsIso₀ M).hom x₂ := by
    intro g
    have key : (d₀₁ M).hom ((cochainsIso₀ M).hom.hom x₂) =
        (cochainsIso₁ M).hom.hom (((inhomogeneousCochains M).d 0 1).hom x₂) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, comp_d₀₁_eq]; rfl
    rw [show ((inhomogeneousCochains M).d 0 1).hom x₂ = 0 from hd, map_zero] at key
    have := congr_fun key g
    exact sub_eq_zero.mp this
  obtain ⟨y, hy⟩ := h _ hinv
  refine ⟨(chainsIso₀ M).inv y, ?_⟩
  simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change (cochainsIso₀ M).inv (M.ρ.norm y) = x₂
  rw [hy, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_neg_one_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, M.ρ.norm m = 0 → ∃ z : G →₀ M, d₁₀ M z = m) :
    IsZero (tateCohomology M (-1)) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousChains M).X 0, M.tateNorm x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 1, (inhomogeneousChains M).d 1 0 x₁ = x₂
  intro x₂ hx
  have hn : M.ρ.norm ((chainsIso₀ M).hom x₂) = 0 := by
    have := congr_arg (fun x => (cochainsIso₀ M).hom x) hx
    simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, map_zero] at this
    exact this
  obtain ⟨z, hz⟩ := h _ hn
  refine ⟨(chainsIso₁ M).inv z, ?_⟩
  rw [eq_d₁₀_comp_inv_apply, hz, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_zero_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M 0) := by
  refine isZero_tateCohomology_zero_of_forall M fun m hm => ⟨φ m, ?_⟩
  rw [Representation.norm, LinearMap.sum_apply]
  conv_rhs => rw [← hφ m]
  simp only [hm]

theorem isZero_tateCohomology_neg_one_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M (-1)) := by
  refine isZero_tateCohomology_neg_one_of_forall M fun m hm =>
    ⟨∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m)), ?_⟩
  have hsum : ∑ g : G, M.ρ g⁻¹ m = M.ρ.norm m := by
    rw [Representation.norm, LinearMap.sum_apply]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
  show (Finsupp.lsum k fun g : G => M.ρ g⁻¹ - LinearMap.id)
    (∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m))) = m

  simp only [map_sum, Finsupp.lsum_single, LinearMap.sub_apply, LinearMap.id_apply, inv_inv]

  rw [Finset.sum_sub_distrib, ← map_sum, hsum, hm, map_zero, sub_zero, hφ]

section Coind

variable (B : Rep.{u} k (⊥ : Subgroup G))


open scoped Classical in
noncomputable def coindBotProj :
    (coind (⊥ : Subgroup G).subtype B).V →ₗ[k] (coind (⊥ : Subgroup G).subtype B).V := by
  classical
  exact LinearMap.codRestrict _ ((LinearMap.single k (fun _ : G => B.V) 1) ∘ₗ LinearMap.proj 1 ∘ₗ
    (Representation.coindV (⊥ : Subgroup G).subtype B.ρ).subtype) fun f => by
      rw [Representation.mem_coindV]
      intro s x
      obtain rfl : s = 1 := Subsingleton.elim _ _
      simp


open scoped Classical in
theorem sum_coindBotProj (f : coind (⊥ : Subgroup G).subtype B) :
    ∑ g : G, (coind (⊥ : Subgroup G).subtype B).ρ g
      (coindBotProj B ((coind (⊥ : Subgroup G).subtype B).ρ g⁻¹ f)) = f := by
  classical
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  change ∑ g : G, (Pi.single (M := fun _ : G => B.V) (1 : G) (f.1 (1 * g⁻¹)) (x * g)) = f.1 x
  rw [Fintype.sum_eq_single x⁻¹]
  · simp
  · intro g hg
    rw [Pi.single_apply, if_neg]
    exact fun h => hg (eq_inv_of_mul_eq_one_right h)

theorem isZero_tateCohomology_coind_bot (n : ℤ) :
    IsZero (tateCohomology (coind (⊥ : Subgroup G).subtype B) n) := by
  classical
  rcases n with (_ | n) | (_ | n)
  · exact isZero_tateCohomology_zero_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · exact ((isZero_groupCohomology_succ_of_subsingleton B n).of_iso (coindIso B (n + 1))).of_iso
      ((TateCohomology.isoGroupCohomology (n + 1)).app _)
  · exact isZero_tateCohomology_neg_one_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · have e := (TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
      (by simp [Int.negSucc_eq])).app (coind (⊥ : Subgroup G).subtype B)
    refine (((isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (indIso (⊥ : Subgroup G) B (n + 1))).of_iso ?_).of_iso e
    exact (groupHomology.functor k G (n + 1)).mapIso (indCoindIso B).symm

theorem isZero_tateCohomology_ind_bot (n : ℤ) :
    IsZero (tateCohomology (ind (⊥ : Subgroup G).subtype B) n) := by
  classical
  exact (isZero_tateCohomology_coind_bot B n).of_iso
    ((tateCohomologyFunctor n).mapIso (indCoindIso B))

theorem tateAcyclic_coind_bot : TateAcyclic (coind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_coind_bot B

theorem tateAcyclic_ind_bot : TateAcyclic (ind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_ind_bot B

end Coind

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open Representation

section Fixed

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]

theorem exists_fixed_mem_span_orbit (hG : IsPGroup p G) (ρ : Representation k G V) {m : V}
    (hm : m ≠ 0) :
    ∃ v ∈ Submodule.span k (Set.range fun g : G => ρ g m), v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  classical
  have hp : ∀ x : V, p • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  let cast : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  let f : (G → ZMod p) →+ V :=
    { toFun := fun c => ∑ g, cast (c g) • ρ g m
      map_zero' := by simp
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }
  have hf : ∀ c, f c = ∑ g, cast (c g) • ρ g m := fun _ => rfl
  have hstab : ∀ (h : G) (c : G → ZMod p), ρ h (f c) = f (fun g => c (h⁻¹ * g)) := by
    intro h c

    rw [hf, hf, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp [map_mul, Module.End.mul_apply]
  have hmem : ∀ (h : G) (x : V), x ∈ f.range → ρ h x ∈ f.range := by
    rintro h x ⟨c, rfl⟩
    exact ⟨fun g => c (h⁻¹ * g), (hstab h c).symm⟩
  have : Finite f.range :=
    Finite.of_injective (fun x : f.range => (⟨x.1, AddMonoidHom.mem_range.mp x.2⟩ : Set.range f))
      fun a b h => Subtype.ext (congrArg Subtype.val h)
  let : MulAction G f.range :=
    { smul := fun h x => ⟨ρ h x, hmem h x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ρ 1 (x : V) = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ρ (a * b) (x : V) = ρ a (ρ b x)
        rw [map_mul, Module.End.mul_apply]) }
  have hm' : m ∈ f.range := ⟨Pi.single 1 1, by
    rw [hf, Fintype.sum_eq_single (1 : G) (fun g hg => by simp [hg])]
    simp⟩
  have horder : addOrderOf (⟨m, hm'⟩ : f.range) = p :=
    addOrderOf_eq_prime (Subtype.ext (by simpa using hp m))
      (fun h => hm (congrArg Subtype.val h))
  have hdvd : p ∣ Nat.card f.range := by
    have := addOrderOf_dvd_natCard (⟨m, hm'⟩ : f.range)
    rwa [horder] at this
  have h0 : (0 : f.range) ∈ MulAction.fixedPoints G f.range := fun g => Subtype.ext (by
    change ρ g 0 = 0
    simp)
  obtain ⟨b, hb, hb0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point f.range hdvd h0
  refine ⟨b.1, ?_, fun h => hb0 (Subtype.ext h.symm), fun g => congrArg Subtype.val (hb g)⟩
  obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.mp b.2
  rw [← hc, hf]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end Fixed

section Nakayama

variable {k G V : Type*} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]

theorem eq_top_of_sup_coinvariantsKer_eq_top (hG : IsPGroup p G) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g : G, W ≤ W.comap (ρ g)) (h : W ⊔ Coinvariants.ker ρ = ⊤) :
    W = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
  obtain ⟨v, hvspan, hv0, hvfix⟩ := exists_fixed_mem_span_orbit hG ρ.dual hf0
  have hd : ∀ (g : G) (φ : Module.Dual k V) (x : V), ρ.dual g φ x = φ (ρ g⁻¹ x) :=
    fun _ _ _ => rfl

  have hvW : W ≤ LinearMap.ker v := by
    have hle : Submodule.span k (Set.range fun g : G => ρ.dual g f) ≤ W.dualAnnihilator := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
      intro w hw
      rw [hd]
      exact hWf (hW g⁻¹ hw)
    intro w hw
    exact (Submodule.mem_dualAnnihilator v).mp (hle hvspan) w hw

  have hvI : Coinvariants.ker ρ ≤ LinearMap.ker v := by
    rw [Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    have := congrArg (fun φ : Module.Dual k V => φ x) (hvfix g⁻¹)
    simp only [hd, inv_inv] at this
    simp [this]
  apply hv0
  ext x
  have hx : x ∈ W ⊔ Coinvariants.ker ρ := h ▸ Submodule.mem_top
  exact (sup_le hvW hvI) hx

theorem subsingleton_of_coinvariantsKer_eq_top (hG : IsPGroup p G) (ρ : Representation k G V)
    (h : Coinvariants.ker ρ = ⊤) : Subsingleton V := by
  have hbot := eq_top_of_sup_coinvariantsKer_eq_top hG ρ ⊥ (fun _ => bot_le) (by rw [bot_sup_eq, h])
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Submodule k V) := hbot ▸ Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule k V) := hbot ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at hx hy
  rw [hx, hy]

end Nakayama

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable (k G : Type u) [CommRing k] [Group G] (X : Type u) [AddCommGroup X] [Module k X]

noncomputable def coindOneRep : Representation k G (G → X) where
  toFun g := LinearMap.funLeft k X (· * g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

noncomputable abbrev coindOne : Rep k G := Rep.of (coindOneRep k G X)

instance : Subsingleton (⊥ : Subgroup G) :=
  ⟨fun a b => Subtype.ext <| by rw [Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2]⟩

noncomputable def coindOneIsoCoind :
    coindOne k G X ≅ coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) X) :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F => ⟨F, fun g h => by rw [Subsingleton.elim g 1]; simp⟩
      invFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun _ => LinearMap.ext fun _ => Subtype.ext rfl)

theorem isZero_coindOne (n : ℕ) : Limits.IsZero (groupCohomology (coindOne k G X) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton (Rep.trivial k (⊥ : Subgroup G) X) n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (coindOneIsoCoind k G X) ≪≫
      groupCohomology.coindIso _ (n + 1))

variable {G} (S : Subgroup G)

lemma out_inv_mul_mem (x : G) : ((x : G ⧸ S).out)⁻¹ * x ∈ S :=
  QuotientGroup.leftRel_apply.1 (Quotient.exact' (QuotientGroup.out_eq' (x : G ⧸ S)))

noncomputable def cosetPart (x : G) : S := ⟨((x : G ⧸ S).out)⁻¹ * x, out_inv_mul_mem S x⟩

lemma out_mul_cosetPart (x : G) : (x : G ⧸ S).out * (cosetPart S x : G) = x := by
  simp [cosetPart]

lemma mk_out_mul (c : G ⧸ S) (s : S) : ((c.out * s : G) : G ⧸ S) = c := by
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  exact (QuotientGroup.eq).2 (by simp)

lemma cosetPart_out_mul (c : G ⧸ S) (s : S) : cosetPart S (c.out * s) = s := by
  apply Subtype.ext
  simp [cosetPart]

noncomputable def resCoindOneIso :
    res S.subtype (coindOne k G X) ≅ coindOne k S (G ⧸ S → X) :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F s c => F (c.out * s)
      invFun := fun F x => F (cosetPart S x) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun F => funext fun x => by
        simp only
        rw [out_mul_cosetPart]
      right_inv := fun F => funext fun s => funext fun c => by
        simp only
        rw [cosetPart_out_mul, mk_out_mul] }
    (fun t => LinearMap.ext fun F => funext fun s => funext fun c => by
      change F ((c.out * s) * t) = F (c.out * ((s * t : S) : G))
      simp [mul_assoc])

noncomputable def quotientToInvariantsCoindOneIso [S.Normal] :
    (coindOne k G X).quotientToInvariants S ≅ coindOne k (G ⧸ S) X :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F c => Quotient.liftOn' c F.1 fun x y hxy => by
        have h := congrFun (F.2 ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.1 hxy⟩) x
        change F.1 (x * (x⁻¹ * y)) = F.1 x at h
        simpa using h.symm
      invFun := fun F => ⟨fun x => F x, fun s => funext fun x => by
        change F (↑(x * (s : G)) : G ⧸ S) = F (x : G ⧸ S)
        exact congrArg F (QuotientGroup.eq.2 (by simp))⟩
      map_add' := fun F F' => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl
      map_smul' := fun r F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl
      left_inv := fun F => Subtype.ext rfl
      right_inv := fun F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl }
    (fun g => by
      induction g using QuotientGroup.induction_on
      exact LinearMap.ext fun F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl)

theorem isZero_res_coindOne (n : ℕ) :
    Limits.IsZero (groupCohomology (res S.subtype (coindOne k G X)) (n + 1)) :=
  (isZero_coindOne k S (G ⧸ S → X) n).of_iso
    ((groupCohomology.functor k S (n + 1)).mapIso (resCoindOneIso k X S))

theorem isZero_quotientToInvariants_coindOne [S.Normal] (n : ℕ) :
    Limits.IsZero (groupCohomology ((coindOne k G X).quotientToInvariants S) (n + 1)) :=
  (isZero_coindOne k (G ⧸ S) X n).of_iso
    ((groupCohomology.functor k (G ⧸ S) (n + 1)).mapIso (quotientToInvariantsCoindOneIso k X S))

end GroundTheory.GroupCoh
end
