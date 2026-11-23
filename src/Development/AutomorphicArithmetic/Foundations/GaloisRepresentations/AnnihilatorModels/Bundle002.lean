module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem mem_baseChange_iInf_ker_sub_id_of_baseChange_eq {F L X ι : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup X] [Module F X] (A : ι → X →ₗ[F] X) (z : L ⊗[F] X)
    (hz : ∀ k, (A k).baseChange L z = z) :
    z ∈ (⨅ k, LinearMap.ker (A k - LinearMap.id)).baseChange L := by
  let b := Module.Free.chooseBasis F L
  let e : L ⊗[F] X ≃ₗ[F] (Module.Free.ChooseBasisIndex F L →₀ X) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl F X)).trans (finsuppScalarLeft F X _)
  have nat : ∀ (f : X →ₗ[F] X) (w : L ⊗[F] X) j, e (f.baseChange L w) j = f (e w j) := by
    intro f w j
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [e, finsuppScalarLeft_apply_tmul_apply]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  have hmem : ∀ j, e z j ∈ ⨅ k, LinearMap.ker (A k - LinearMap.id) := by
    intro j
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro k
    have h := congrArg (fun w => e w j) (hz k)
    simpa only [nat] using h
  have hsingle : ∀ j (x : X), e.symm (Finsupp.single j x) = b j ⊗ₜ[F] x := by
    intro j x
    simp [e]
  have hz' : z = (e z).sum (fun j x => b j ⊗ₜ[F] x) := by
    conv_lhs => rw [← e.symm_apply_apply z, ← Finsupp.sum_single (e z)]

    simp only [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hsingle j _
  rw [hz']
  exact Submodule.sum_mem _ fun j _ => Submodule.tmul_mem_baseChange_of_mem _ (hmem j)

theorem UpperTheory.Gal.crystallineComparison.dinvExt_of :
    DinvExt := by
  unfold DinvExt
  intro F G B _ _ _ _ σ L _ _ V _ _ ρ
  let T : G → (V ⊗[F] B) →ₗ[F] (V ⊗[F] B) := fun g => AlgebraTensorModule.map (ρ g) (σ g)
  have hD : Dinv σ ρ = ⨅ g, LinearMap.ker (T g - LinearMap.id) := rfl
  have comm : ∀ g (w : (L ⊗[F] V) ⊗[F] B),
      AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (extRep L ρ g) (σ g) w) =
        (T g).baseChange L (AlgebraTensorModule.assoc F F L L V B w) := by
    intro g w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u c =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a v => simp [T, extRep, AlgebraTensorModule.map_tmul]
      | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add (f := _), h₁, h₂]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  ext z
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hz
    rw [hD]
    apply mem_baseChange_iInf_ker_sub_id_of_baseChange_eq
    intro g
    have h : AlgebraTensorModule.map (extRep L ρ g) (σ g)
        ((AlgebraTensorModule.assoc F F L L V B).symm z) =
          (AlgebraTensorModule.assoc F F L L V B).symm z := by
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hz
      exact hz g
    have h2 := congrArg (AlgebraTensorModule.assoc F F L L V B) h
    rwa [comm, LinearEquiv.apply_symm_apply] at h2
  · intro hz
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    rw [comm, LinearEquiv.apply_symm_apply]
    obtain ⟨w, rfl⟩ := hz
    have hfix : T g ∘ₗ (Dinv σ ρ).subtype = (Dinv σ ρ).subtype := by
      refine LinearMap.ext fun s => ?_
      have hs := s.2
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hs
      exact hs g
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hfix]
end

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.annExt_of :
    DinvExt → AnnExt := by
  intro h F G B _ _ _ _ σ ψ L _ _ V _ _ ρ
  have hD := h F G B σ L V ρ
  have hinj : Function.Injective ((Dinv σ ρ).subtype.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Dinv σ ρ).injective_subtype
  refine ⟨fun e hadm => ?_, fun q n T hA x hx => ?_⟩
  · unfold admitted at hadm ⊢
    rw [← LinearEquiv.finrank_map_eq (AlgebraTensorModule.assoc F F L L V B), hD, Module.finrank_baseChange]
    rw [← hadm]
    change Module.finrank L (LinearMap.range ((Dinv σ ρ).subtype.baseChange L)) = _
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
  · unfold AnnD at hA
    dsimp only
    have comm : ∀ (f : V →ₗ[F] V) (g : B →ₗ[F] B) (y : (L ⊗[F] V) ⊗[F] B),
        AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (f.baseChange L) g y) =
          (AlgebraTensorModule.map f g).lTensor L (AlgebraTensorModule.assoc F F L L V B y) := by
      intro f g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul u b =>
        induction u using TensorProduct.induction_on with
        | zero => simp
        | tmul a v => simp
        | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add (f := _), h₁, h₂]
      | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
    have hmem : AlgebraTensorModule.assoc F F L L V B x ∈ (Dinv σ ρ).baseChange L := by
      rw [← hD]
      exact Submodule.mem_map_of_mem hx
    apply (AlgebraTensorModule.assoc F F L L V B).injective

    rw [map_sum, map_zero]
    simp only [map_zsmul, comm]
    obtain ⟨z, hz⟩ := Submodule.toBaseChange_surjective' L (Dinv σ ρ) hmem
    rw [← hz]
    clear hz hmem
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
      simp only [Submodule.coe_toBaseChange_tmul, LinearMap.lTensor_tmul]
      have := hA w w.2
      calc _ = TensorProduct.mk F L (V ⊗[F] B) a (∑ j ∈ Finset.range (n + 1), ((-1) ^ j * (q : ℤ) ^ j.choose 2) • (AlgebraTensorModule.map (T j) (ψ ^ (n - j))) w) := by

            simp only [map_sum, map_zsmul, TensorProduct.mk_apply]
        _ = 0 := by rw [this, map_zero]
    | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), Submodule.coe_add, Finset.sum_add_distrib, smul_add, h₁, h₂, add_zero]
end

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem algebraTensorModule_map_map_id_left_comm_of_comm {F L V B B' : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']
    (c : B →ₗ[F] B') (f : V →ₗ[L] V) (u : B →ₗ[F] B) (u' : B' →ₗ[F] B')
    (h : ∀ b, c (u b) = u' (c b)) (x : V ⊗[F] B) :
    AlgebraTensorModule.map f u' (AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) c x) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) c (AlgebraTensorModule.map f u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]


theorem UpperTheory.Gal.crystallineComparison.annPer_of :
    AnnPer := by
  intro F G B B' _ _ _ _ _ _ σ ψ σ' ψ' c hc hσ hψ L _ _ e hB V _ _ _ _ _ ρ hA
  unfold Bound at hB
  unfold admitted at hA ⊢
  have hpow : ∀ k b, c ((ψ ^ k) b) = (ψ' ^ k) (c b) := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hψ]
  let m : V ⊗[F] B →ₗ[L] V ⊗[F] B' := AlgebraTensorModule.map LinearMap.id c
  have hm_inj : Function.Injective m := by
    have h1 : ⇑m = ⇑(LinearMap.lTensor V c) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h1]
    exact Module.Flat.lTensor_preserves_injective_linearMap c hc
  have hmaps : ∀ x ∈ Dinv σ ρ, m x ∈ Dinv σ' ρ := by
    intro x hx
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    exact (algebraTensorModule_map_map_id_left_comm_of_comm c (ρ g) (σ g) (σ' g) (hσ g) x).trans (congrArg m (hx g))
  let φ : Dinv σ ρ →ₗ[L] Dinv σ' ρ := m.restrict hmaps
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply hm_inj
    exact congrArg Subtype.val hab
  obtain ⟨hfin', hle⟩ := hB V ρ
  haveI : Module.Finite L (Dinv σ ρ) := Module.Finite.of_injective φ hφ
  have hge : finrank L (Dinv σ ρ) ≤ finrank L (Dinv σ' ρ) :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have heq : finrank L (Dinv σ ρ) = finrank L (Dinv σ' ρ) := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hφ
  refine ⟨by omega, ?_⟩
  intro q n T hT
  unfold AnnD at hT ⊢
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hxy : x = m y.1 := (congrArg Subtype.val hy).symm
  have key : ∀ j, (AlgebraTensorModule.map (T j) (ψ' ^ (n - j))) (m y.1) =
      m ((AlgebraTensorModule.map (T j) (ψ ^ (n - j))) y.1) :=
    fun j => algebraTensorModule_map_map_id_left_comm_of_comm c (T j) (ψ ^ (n - j)) (ψ' ^ (n - j)) (hpow (n - j)) y.1
  have h0 := congrArg m (hT y.1 y.2)

  rw [map_zero, map_sum] at h0
  rw [hxy, ← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j]
  exact (LinearMap.map_smul_of_tower m _ _).symm
end

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.joinAbs_of :
    NilEmb → NilSubq → NilOfAnn → AnnSub → AnnExt → AdmExact → JoinAbs := by
  intro hEmb hSubq hOfAnn hAnnSub hAnnExt hAdmExact
  intro F G B _ _ _ _ σ ψ hσψ L _ _ e hB V _ _ _ ρ q n T hAdm hAnn U _ _ ρU i TU θ hi hinj hT hTg hTT hnil
    W _ _ _ _ ρW I _ C _ _ ρC f hsub hf hsep
  letI : Module F U := Module.compHom _ (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : ∀ a, Module F (C a) := fun a => Module.compHom _ (algebraMap F L)
  haveI : ∀ a, IsScalarTower F L (C a) := fun a => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  obtain ⟨hE1, hE2⟩ := hAnnExt F G B σ ψ L V ρ
  have hAdmL := hE1 e hAdm
  have hAnnL := hE2 q n T hAnn
  have hAdmU : admitted σ e ρU :=
    (hAdmExact F G B σ L e hB U (L ⊗[F] V) ρU (extRep L ρ) i hi).1 hinj hAdmL
  have hAnnU : AnnD σ ψ q n ρU TU :=
    hAnnSub F G B σ ψ L U (L ⊗[F] V) ρU (extRep L ρ) i hi hinj q n TU
      (fun j => (T j).baseChange L) hT hAnnL
  have hNilU : NilD σ ψ ρU (heckePol q n θ) :=
    hOfAnn F G B σ ψ hσψ L U ρU q n TU θ hTg hTT hnil hAnnU
  have hNilC : ∀ a, NilD σ ψ (ρC a) (heckePol q n θ) := fun a =>
    (hSubq F G B σ ψ L e hB U (C a) ρU (ρC a) (hsub a) hAdmU).2 _ hNilU
  exact hEmb F G B σ ψ L W ρW I C ρC f hf hsep _ hNilC
end

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem algebraTensorModule_map_map_id_right_comm_of_comm {F L U V B : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup B] [Module F B]
    (i : U →ₗ[L] V) (f : U →ₗ[L] U) (f' : V →ₗ[L] V) (u : B →ₗ[F] B)
    (h : ∀ a, i (f a) = f' (i a)) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f' u (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) x) =
      AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map f u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]


theorem UpperTheory.Gal.crystallineComparison.annSub_of :
    AnnSub := by
  intro F G B _ _ _ _ σ ψ L _ _ U V _ _ _ _ _ _ _ _ ρU ρ i hI hi q n TU T hT hAnn
  unfold Inter at hI
  unfold AnnD at hAnn ⊢
  let M : U ⊗[F] B →ₗ[L] V ⊗[F] B := AlgebraTensorModule.map i LinearMap.id
  have hM_inj : Function.Injective M := by
    have h1 : ⇑M = ⇑(LinearMap.rTensor B (i.restrictScalars F)) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [M]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h1]
    exact Module.Flat.rTensor_preserves_injective_linearMap (i.restrictScalars F) hi
  have hpow : ∀ k, ∀ b, (LinearMap.id : B →ₗ[F] B) ((ψ ^ k) b) = (ψ ^ k) ((LinearMap.id : B →ₗ[F] B) b) :=
    fun _ _ => rfl
  intro x hx
  have hmx : M x ∈ Dinv σ ρ := by
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    exact (algebraTensorModule_map_map_id_right_comm_of_comm i (ρU g) (ρ g) (σ g) (hI g) x).trans (congrArg M (hx g))
  apply hM_inj

  rw [map_zero, ← hAnn (M x) hmx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower]
  congr 1
  exact (algebraTensorModule_map_map_id_right_comm_of_comm i (TU j) (T j) (ψ ^ (n - j)) (hT j) x).symm
end

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {F B : Type} [Field F] [AddCommGroup B] [Module F B]
  {L : Type} [Field L] [Algebra F L] {V : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]

private abbrev Phi (a : End L V) (b : End F B) : End L (V ⊗[F] B) := AlgebraTensorModule.map a b

end

private theorem commute_tensorMap_of_commute {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {f₁ f₂ : Module.End L V} {g₁ g₂ : Module.End F B} (hf : Commute f₁ f₂) (hg : Commute g₁ g₂) :
    Commute (AlgebraTensorModule.map f₁ g₁ : Module.End L (V ⊗[F] B)) (AlgebraTensorModule.map f₂ g₂) := by
  unfold Commute SemiconjBy
  rw [← AlgebraTensorModule.map_mul, ← AlgebraTensorModule.map_mul, hf.eq, hg.eq]

private theorem tensorMap_pow {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (f : Module.End L V) (g : Module.End F B) (k : ℕ) :
    (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) ^ k = AlgebraTensorModule.map (f ^ k) (g ^ k) := by
  induction k with
  | zero => simp only [pow_zero, AlgebraTensorModule.map_one]
  | succ k ih =>
    rw [pow_succ, ih, ← AlgebraTensorModule.map_mul, ← pow_succ, ← pow_succ]

private theorem isNilpotent_tensorMap_of_isNilpotent {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {f : Module.End L V} (g : Module.End F B) (hf : IsNilpotent f) :
    IsNilpotent (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) := by
  have h : (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) =
      AlgebraTensorModule.map f 1 * AlgebraTensorModule.map 1 g := by
    rw [← AlgebraTensorModule.map_mul, mul_one, one_mul]
  rw [h]
  apply Commute.isNilpotent_mul_right (commute_tensorMap_of_commute (Commute.one_right f) (Commute.one_left g))
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, ?_⟩
  rw [tensorMap_pow, hk, one_pow]
  apply TensorProduct.AlgebraTensorModule.ext
  intro v b
  simp

theorem UpperTheory.Gal.crystallineComparison.nilAnn_of :
    NilOfAnn := by
  intro F G B _ _ _ _ σ ψ hσψ L _ _ V _ _ _ _ ρ q n T θ hTρ hTT hnil hann
  let c : ℕ → ℤ := fun j => (-1) ^ j * (q : ℤ) ^ j.choose 2
  let P : Module.End L (V ⊗[F] B) :=
    ∑ j ∈ Finset.range (n + 1), c j • AlgebraTensorModule.map (T j) (ψ ^ (n - j))
  let E : Module.End L (V ⊗[F] B) :=
    ∑ j ∈ Finset.range (n + 1), c j • AlgebraTensorModule.map (T j - θ j • 1) (ψ ^ (n - j))
  have hQ : Polynomial.aeval (onPer ψ L V) (heckePol q n θ) = P - E := by
    rw [← Finset.sum_sub_distrib]

    simp only [heckePol, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    simp only [onPer, tensorMap_pow, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Module.End.mul_apply, Module.algebraMap_end_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      AlgebraTensorModule.map_tmul, ← smul_sub, ← sub_tmul]
    simp [c, smul_tmul', sub_sub_cancel, smul_smul]
    rw [← Int.cast_smul_eq_zsmul L, smul_smul]
    congr 2
    push_cast
    ring
  have hP : ∀ x ∈ Dinv σ ρ, P x = 0 := by
    intro x hx
    simp only [P, LinearMap.sum_apply, LinearMap.smul_apply]
    exact hann x hx
  have hM : ∀ i j : ℕ, ∀ f : Module.End L V, Commute (T i) f →
      Commute (c i • AlgebraTensorModule.map (T i) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
        (c j • AlgebraTensorModule.map f (ψ ^ (n - j))) := by
    intro i j f hf
    have h0 : Commute (AlgebraTensorModule.map (T i) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
        (AlgebraTensorModule.map f (ψ ^ (n - j))) :=
      commute_tensorMap_of_commute hf (Commute.pow_pow_self ψ _ _)
    exact (h0.smul_left (c i)).smul_right (c j)
  have hPE : Commute P E := by
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
    exact hM i j _ ((hTT i j).sub_right ((Commute.one_right (T i)).smul_right (θ j)))
  have hE : IsNilpotent E := by
    refine Commute.isNilpotent_sum (fun j hj => (isNilpotent_tensorMap_of_isNilpotent _ (hnil j ?_)).smul (c j)) ?_
    · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    · intro i j _ _
      have hf : Commute (T i - θ i • 1) (T j - θ j • 1) := by
        refine ((hTT i j).sub_right ((Commute.one_right (T i)).smul_right (θ j))).sub_left ?_
        exact ((Commute.one_left (T j)).smul_left (θ i)).sub_right
          (((Commute.one_right _).smul_left (θ i)).smul_right (θ j))
      have h0 : Commute (AlgebraTensorModule.map (T i - θ i • 1) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
          (AlgebraTensorModule.map (T j - θ j • 1) (ψ ^ (n - j))) :=
        commute_tensorMap_of_commute hf (Commute.pow_pow_self ψ _ _)
      exact (h0.smul_left (c i)).smul_right (c j)
  obtain ⟨N, hN⟩ := hE
  refine ⟨N, fun x hx => ?_⟩
  have key : ∀ (k : ℕ) (y : V ⊗[F] B), P y = 0 → ((P - E) ^ k) y = ((-E) ^ k) y := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have h1 : (P - E) y = (-E) y := by simp [hy]
      rw [h1]
      apply ih
      rw [← Module.End.mul_apply, hPE.neg_right.eq, Module.End.mul_apply, hy, map_zero]
  rw [hQ, key N x (hP x hx), neg_pow, hN]
  simp
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.baseChart_of :
    BaseOfSmooth → BaseOfChart := by
  intro h
  unfold BaseOfChart
  intro l O _ _ _ ϖ hϖ hl hlu Y g hg U hU
  let φ : O →+* Γ(Y, U) :=
    (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hφ : ∀ a : O, φ a = (Y.presheaf.map (homOfLE le_top).op).hom
      ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) := fun a => rfl
  have hsm : φ.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv)
    · exact HasRingHomProperty.appLE @Smooth g hg ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  letI : Algebra O Γ(Y, U) := φ.toAlgebra
  haveI : Algebra.Smooth O Γ(Y, U) := hsm
  have hb := h l O Γ(Y, U) ϖ hϖ hl hlu
  have hϖφ : (algebraMap O Γ(Y, U)) ϖ = (Y.presheaf.map (homOfLE le_top).op).hom (fn g ϖ) := hφ ϖ
  rw [hϖφ] at hb
  refine ⟨hb, 1, ?_⟩
  have hmem : (l : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hlu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [pow_one, ← hϖφ, Ideal.mem_span_singleton']
  refine ⟨algebraMap O Γ(Y, U) c, ?_⟩
  rw [← map_mul, hc, map_natCast]
end
