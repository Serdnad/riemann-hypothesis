module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem detjac_tprod_ne_zero {α : Type} [Fintype α] {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (y : ∀ a, X a) (hy : ∀ a, y a ≠ 0) : PiTensorProduct.tprod ℂ y ≠ 0 := by
  have hφ : ∀ b, ∃ φ : X b →ₗ[ℂ] ℂ, φ (y b) ≠ 0 := fun b => by
    by_contra! h
    exact hy b ((Module.forall_dual_apply_eq_zero_iff ℂ (y b)).1 h)
  choose φ hφ using hφ
  intro h
  have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap φ)) h
  rw [PiTensorProduct.lift.tprod, map_zero] at h1
  exact Finset.prod_ne_zero_iff.2 (fun b _ => hφ b) (by simpa using h1)

private theorem detjac_scalar_factor {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (hX : ∀ a, Nontrivial (X a)) (j : α) (g : Γ j) (c : ℂ)
    (h : ∀ w, piTensor ρ (Pi.mulSingle j g) w = c • w) (v : X j) : ρ j g v = c • v := by
  choose x hx using fun a => exists_ne (0 : X a)
  have h1 := h (PiTensorProduct.tprod ℂ (Function.update x j v))
  have h2 : (fun a => ρ a ((Pi.mulSingle j g : ∀ a, Γ a) a) (Function.update x j v a)) =
      Function.update x j (ρ j g v) := by
    funext a
    by_cases ha : a = j
    · subst ha; simp
    · simp [Pi.mulSingle_eq_of_ne ha, Function.update_of_ne ha]
  rw [piTensor_tprod, h2] at h1
  have hs : PiTensorProduct.tprod ℂ (Function.update x j (c • v)) =
      c • PiTensorProduct.tprod ℂ (Function.update x j v) := by
    simpa using (PiTensorProduct.tprod ℂ).map_update_smul x j c v
  rw [← hs, ← sub_eq_zero, ← (PiTensorProduct.tprod ℂ).map_update_sub x j] at h1
  by_contra hne
  refine detjac_tprod_ne_zero _ (fun a => ?_) h1
  by_cases ha : a = j
  · subst ha; simpa [sub_eq_zero] using hne
  · simpa [Function.update_of_ne ha] using hx a

private theorem detjac_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : jhMult σ ρ ≠ 0) :
    IsSubquotient σ ρ := by
  by_contra hn
  refine h ?_
  simp only [jhMult, ENat.iSup_eq_zero]
  rintro r ⟨S, T, -, -, h3⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rfl
  obtain ⟨φ⟩ := h3 ⟨0, hr⟩
  refine absurd ?_ hn
  refine (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans ?_
  exact ⟨S ⟨0, hr⟩, ⟨Submodule.mkQ _, fun g => rfl⟩, Submodule.mkQ_surjective _⟩

private theorem detjac_equiv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    (hi : π.IsIrreducible) (ψ : G →* ℂˣ) (h : ∀ g v, π g v = (ψ g : ℂ) • v) : Nonempty ((ofChar ψ).Equiv π) := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let f : (ofChar ψ).IntertwiningMap π := ⟨LinearMap.toSpanSingleton ℂ V x, fun g => LinearMap.ext fun c => by
    simp [h, smul_smul]⟩
  have hinj : Function.Injective f := smul_left_injective ℂ hx
  refine ⟨equivOfBijective f ⟨hinj, ?_⟩⟩
  rcases eq_bot_or_eq_top f.range with h0 | h0
  · have : x ∈ f.range := ⟨1, one_smul _ _⟩
    rw [h0] at this
    exact absurd this hx
  · intro v
    have : v ∈ f.range := by rw [h0]; trivial
    exact this

theorem UpperTheory.Lit.Mix.detjac :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = t), 0 < (q 0).1 → jm q hq (detRep (Fin t) χ) ≠ 0 → ∃ A : Multiset (IrrGL (k := k)), HasSupport (q 0).rep A ∧ (IrrGL.ofChar χ hχ).nu (-((t : ℂ) - 1) / 2) ∈ A := by
  intro k _ _ _ _ t χ hχ q hq hpos hj
  have hsub := detjac_isSubquotient hj
  have hχ' : IsSmoothChar (χ * absPow k (-((t : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
  have hm : modExp (fun i : Fin 2 => Fin (q i).1) 0 = (q 1).1 := by
    have h1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
    simp [modExp, h1]
  have hc : χ * absPow k (-(modExp (fun i : Fin 2 => Fin (q i).1) 0 : ℂ) / 2) =
      (χ * absPow k (-((t : ℂ) - 1) / 2)) * absPow k (((((q 0).1 : ℕ) : ℂ) - 1) / 2) := by
    rw [mul_assoc, ← absPow_add, hm, ← hq, Fin.sum_univ_two]
    congr 2
    push_cast
    ring
  have hact : ∀ g v, (q 0).rep g v = ((detChar (Fin (q 0).1)
      ((χ * absPow k (-((t : ℂ) - 1) / 2)) * absPow k (((((q 0).1 : ℕ) : ℂ) - 1) / 2))) g : ℂ) • v := by
    intro g v
    refine detjac_scalar_factor (fun a => (q a).rep)
      (fun a => Model.nontrivial_of_isIrreducible (q a).2.rep.irr) 0 g _ (fun w => ?_) v
    rw [Model.scalar_of_isSubquotient hsub (Model.jac_detRep _ χ _) w, detLevi_apply, Fin.prod_univ_two,
      Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide), map_one, map_one, mul_one, hc, detChar_apply]
  obtain ⟨φ⟩ := detjac_equiv (q 0).2.rep.irr _ hact
  refine ⟨_, (hasSupport_detRep hχ' hpos).of_equiv φ, ?_⟩
  refine Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, hpos, ?_⟩)
  rw [Nat.cast_zero, IrrGL.nu_zero, IrrGL.nu, IrrGL.tw_ofChar]
  rfl
end

section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem sum_card_mul_modExp {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] :
    ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

private theorem deltaHalf_scalar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (t : kˣ) :
    (deltaHalf k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) : ℂ) = 1 := by
  rw [val_deltaHalf]
  have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
  have hn : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (m a) t)) =
      nabs k t ^ ((Fintype.card (m a) : ℤ)) := by
    intro a
    rw [Matrix.GeneralLinearGroup.det_scalar, zpow_natCast]
    simp [nabs, map_pow]
  have key : ∀ (s : Finset α) (f : α → ℤ), ∏ a ∈ s, nabs k t ^ f a = nabs k t ^ (∑ a ∈ s, f a) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]
  have hmod : modulus k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
    simp only [modulus, hn, ← zpow_mul]
    rw [key, sum_card_mul_modExp, zpow_zero]
  rw [hmod]
  simp

private theorem parInd_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α n W : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (t : kˣ) (c : ℂ)
    (hρ : ∀ w, ρ (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) w = c • w) (v : IndSp e ρ) :
    parInd e ρ (Matrix.GeneralLinearGroup.scalar n t) v = c • v := by
  have hmem : Matrix.GeneralLinearGroup.scalar n t ∈ parab k e := by
    rw [mem_parab]
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    simp [Matrix.GeneralLinearGroup.scalar, hne]
  have hproj : leviProj k e ⟨_, hmem⟩ = fun a => Matrix.GeneralLinearGroup.scalar (m a) t := by
    funext a
    ext i j
    simp [leviProj, diagBlock, Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, e.injective.eq_iff,
      Matrix.diagonal_apply, Sigma.mk.inj_iff]
  have hcomm : ∀ x : GL n k, x * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * x := by
    intro x
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, mul_comm]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  show v.1.1 (x * Matrix.GeneralLinearGroup.scalar n t) = (c • v).1.1 x
  rw [hcomm x]
  have hlaw := parInd_law e ρ v ⟨_, hmem⟩ x
  simp only at hlaw
  rw [hlaw, hproj, deltaHalf_scalar, hρ, one_smul]
  rfl

private theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (hc : ∀ a v, ρ a (g a) v = c a • v) : ∀ w, piTensor ρ g w = (∏ i, c i) • w := by
  intro w
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [LinearMap.map_smul, piTensor_tprod]
    simp only [hc]
    rw [MultilinearMap.map_smul_univ, smul_comm]
    simp only [RingHom.id_apply]
  | add x y hx hy =>
    rw [map_add (f := _), hx, hy, smul_add]

theorem UpperTheory.Lit.Cas.scalarFull :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (y : Fin h → IrrGL (k := k)) (hc : ∑ i, (y i).1 = N) (t : kˣ) (c : Fin h → ℂ), (∀ i, ScalarBy (y i) t (c i)) → ∀ v, prodIrr y hc (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = (∏ i, c i) • v := by
  intro k _ _ _ _ h N y hc t c hy v
  exact parInd_scalar (stdBlocks (fun a => (y a).1) hc) (piTensor fun a => (y a).rep) t (∏ i, c i)
    (piTensor_scalar (fun a => (y a).rep) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (y a).1) t) c
      (fun a w => hy a w)) v
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

namespace UpperTheory.Lit.Red

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def FirstIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = x.1), (q 0).IsCusp → jm q hq x.rep ≠ 0 → q 0 ∈ P

def LastIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = x.1), (q 1).IsCusp → jm q hq x.rep ≠ 0 → q 1 ∈ P

def SuppIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∃ A : Multiset (IrrGL (k := k)), HasSupport x.rep A ∧ ∀ y ∈ A, y ∈ P

def Emb (x y z : IrrGL (k := k)) : Prop :=
  ∃ (hd : ∑ a, (![y, z] a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr ![y, z] hd)), Function.Injective f

def Occ (x y z : IrrGL (k := k)) : Prop :=
  ∃ hd : ∑ a, (![y, z] a).1 = x.1, jhMult x.rep (prodIrr ![y, z] hd) ≠ 0

def up (ρ : IrrGL (k := k)) : Set (IrrGL (k := k)) := {y | ∃ n : ℕ, y = ρ.nu (n : ℂ)}

end UpperTheory.Lit.Red

end
end

section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem UpperTheory.Lit.Cas.schur_adm : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → GlobalTheory.PRep.IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id :=
  _root_.UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm

private theorem UpperTheory.Lit.Cas.exists_ne_zero_of_irr {G N : Type} [Group G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) (hirr : π.IsIrreducible) : ∃ x : N, x ≠ 0 := by
  have hne : (⊥ : Subrepresentation π) ≠ ⊤ := bot_ne_top
  by_contra h
  push Not at h
  apply hne
  ext v
  simp [h v]

theorem UpperTheory.Lit.Cas.schur :
    GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ), (∃ c, ScalarBy x t c) ∧ (∀ c c', ScalarBy x t c → ScalarBy x t c' → c = c') ∧ ∀ c, x.1 = 0 → ScalarBy x t c → c = 1 := by
  intro H k _ _ _ _ x t
  obtain ⟨v, hv⟩ := UpperTheory.Lit.Cas.exists_ne_zero_of_irr x.rep x.2.rep.irr
  have uniq : ∀ c c', ScalarBy x t c → ScalarBy x t c' → c = c' := fun c c' h h' =>
    smul_left_injective ℂ hv ((h v).symm.trans (h' v))
  refine ⟨?_, uniq, fun c h0 hc => uniq _ _ hc fun w => ?_⟩
  · obtain ⟨c, hc⟩ := UpperTheory.Lit.Cas.schur_adm (GL (Fin x.1) k) (KO k (Fin x.1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ x.rep x.2.rep.irr (H k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr)
      (x.rep (Matrix.GeneralLinearGroup.scalar (Fin x.1) t)) (fun g w => by
        have hcomm : Matrix.GeneralLinearGroup.scalar (Fin x.1) t * g =
            g * Matrix.GeneralLinearGroup.scalar (Fin x.1) t := by
          apply Units.ext
          exact (Matrix.scalar_commute (n := Fin x.1) (t : k) (fun r => Commute.all _ _) (g : Matrix _ _ k)).eq
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply])
    exact ⟨c, fun w => by rw [hc]; rfl⟩
  · haveI : IsEmpty (Fin x.1) := by rw [h0]; infer_instance
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin x.1) t = 1 :=
      Units.ext (Matrix.ext fun i => isEmptyElim i)
    rw [h1, map_one, one_smul]; rfl
end
