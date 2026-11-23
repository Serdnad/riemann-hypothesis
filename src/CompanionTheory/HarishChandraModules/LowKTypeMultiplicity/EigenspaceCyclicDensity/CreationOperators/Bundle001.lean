module

import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FinsetCAR
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset

noncomputable section

namespace CompanionTheory.D.LK.Car

variable {n : ℕ}

theorem key_inj {i j : Pos n} (h : key i = key j) : i = j := by
  apply Subtype.ext (finProdFinEquiv.injective (Fin.ext ?_))
  change (i.1.2 : ℕ) + n * (i.1.1 : ℕ) = (j.1.2 : ℕ) + n * (j.1.1 : ℕ)
  unfold key at h
  simpa [Nat.mul_comm, Nat.add_comm] using h

def tw (i j : Pos n) : ℂ := if key j < key i then -1 else 1

theorem tw_self (i : Pos n) : tw i i = 1 := by
  simp [tw]

theorem tw_mul_self (i j : Pos n) : tw i j * tw i j = 1 :=
  _root_.CompanionTheory.FinsetCAR.tw_mul_self key i j

theorem tw_swap {i j : Pos n} (h : i ≠ j) : tw j i = -tw i j :=
  _root_.CompanionTheory.FinsetCAR.tw_swap key (fun _ _ h => key_inj h) h

theorem sg_mul_self (i : Pos n) (A : Finset (Pos n)) : sg i A * sg i A = 1 :=
  _root_.CompanionTheory.FinsetCAR.sg_mul_self key i A

theorem sg_insert (i : Pos n) {j : Pos n} {A : Finset (Pos n)} (h : j ∉ A) :
    sg i (insert j A) = tw i j * sg i A :=
  _root_.CompanionTheory.FinsetCAR.sg_insert key i h

theorem sg_erase (i : Pos n) {j : Pos n} {A : Finset (Pos n)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A :=
  _root_.CompanionTheory.FinsetCAR.sg_erase key i h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_apply (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl

theorem cre_apply (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl

theorem ann_ann (i j : Pos n) : (ann i * ann j + ann j * ann i : Module.End ℂ (Cn n V)) = 0 :=
  _root_.CompanionTheory.FinsetCAR.ann_ann key (fun _ _ h => key_inj h) i j

theorem cre_cre (i j : Pos n) : (cre i * cre j + cre j * cre i : Module.End ℂ (Cn n V)) = 0 :=
  _root_.CompanionTheory.FinsetCAR.cre_cre key (fun _ _ h => key_inj h) i j

theorem ann_cre (i j : Pos n) :
    (ann i * cre j + cre j * ann i : Module.End ℂ (Cn n V)) = if i = j then 1 else 0 :=
  _root_.CompanionTheory.FinsetCAR.ann_cre key (fun _ _ h => key_inj h) i j


end CompanionTheory.D.LK.Car
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.LKDens

open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem burnside {A : Type} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hnt : Nontrivial V) (hirr : ∀ W : Submodule ℂ V, (∀ a : A, ∀ w ∈ W, ρ a w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  classical
  letI : Module A V := Module.compHom V (ρ : A →+* Module.End ℂ V)
  have hsm : ∀ (a : A) (x : V), a • x = ρ a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ A V := ⟨fun c a x => by simp [hsm]⟩
  haveI : IsSimpleModule A V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun W => ?_ }
    rcases hirr (W.restrictScalars ℂ) (fun a w hw => W.smul_mem a hw) with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 h
    · right; exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 h
  have hscal : ∀ φ : Module.End A V, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  intro f
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis ℂ V
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  exact (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).symm

def rho (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ L :=
  FreeAlgebra.lift ℂ fun p => if h : ε p.1 = ε p.2 then (E p.1 p.2).restrict (hL p.1 p.2 h) else 0

def psi (ε : Fin n → Bool) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => if ε p.1 = ε p.2 then FreeAlgebra.ι ℂ p else 0

theorem ev_psi (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    (r : FreeAlgebra ℂ (Fin n × Fin n)) : ∀ s : L, ev E (psi ε r) s = (rho ε E L hL r s : V) := by
  induction r using FreeAlgebra.induction with
  | grade0 c => intro s; simp [Module.algebraMap_end_apply]
  | grade1 p =>
    intro s
    by_cases h : ε p.1 = ε p.2
    · simp [psi, rho, ev, h]
    · simp [psi, rho, ev, h]
  | mul a b ha hb => intro s; simp [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro s; simp [map_add (f := _), ha, hb]

theorem rho_surj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    [FiniteDimensional ℂ L] {v : V} (hv : v ≠ 0) (hvL : v ∈ L)
    (hirr : ∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) : Function.Surjective (rho ε E L hL) := by
  refine burnside (rho ε E L hL) ⟨⟨v, hvL⟩, 0, fun h => hv (congrArg Subtype.val h)⟩ ?_
  intro W hW
  have hst : KStab ε E (W.map L.subtype) := by
    rintro a b hab _ ⟨w, hw, rfl⟩
    refine ⟨rho ε E L hL (FreeAlgebra.ι ℂ (a, b)) w, hW _ w hw, ?_⟩
    simp [rho, hab]
  rcases hirr _ (Submodule.map_subtype_le L W) hst with h | h
  · left
    apply Submodule.map_injective_of_injective L.injective_subtype
    simpa using h
  · right
    apply Submodule.map_injective_of_injective L.injective_subtype
    simpa using h

theorem dens : CompanionTheory.D.LK.Dens := by
  intro n ε V _ _ E μ v L _ _ hv hvL _ hfd hL hirr _
  have hs := rho_surj ε E L hL hv hvL hirr
  let b := Module.finBasis ℂ L
  constructor
  · intro x hx
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ
      (show (⟨v, hvL⟩ : L) ≠ 0 from fun h => hv (congrArg Subtype.val h))
    obtain ⟨r, hr⟩ := hs (f.smulRight (⟨x, hx⟩ : L))
    refine ⟨psi ε r, ?_⟩
    have := ev_psi ε E L hL r ⟨v, hvL⟩
    rw [hr] at this
    simpa [hf] using this
  · intro φ hφ
    choose u hu using fun i => hφ (b i)
    choose r hr using fun i => hs ((b.coord i).smulRight (⟨v, hvL⟩ : L))
    refine ⟨∑ i, u i * psi ε (r i), fun s => ?_⟩
    have hu' : ∀ i, ev E (u i) v = φ (b i) := fun i => by simpa using hu i
    conv_rhs => rw [← b.sum_repr s]

    simp only [map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply, ev_psi ε E L hL, hr, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hu']

end GlobalTheory.CompanionTheory.LKDens
end
end

section

open Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LKWtProj

open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KRel KUnit KStab)

theorem exists_proj {M : Type} [AddCommGroup M] [Module ℂ M] (F : Module.End ℂ M) (τ : ℂ) (t : M)
    (ht : t ∈ ⨆ μ : ℂ, F.eigenspace μ) :
    ∃ P : Module.End ℂ M, (∀ G, Commute F G → Commute P G) ∧
      (∀ W : Submodule ℂ M, (∀ x ∈ W, F x ∈ W) → ∀ x ∈ W, P x ∈ W) ∧
      (∀ y, F y = τ • y → P y = y) ∧ F (P t) = τ • P t := by
  induction ht using Submodule.iSup_induction' with
  | mem μ x hx =>
    rw [Module.End.mem_eigenspace_iff] at hx
    by_cases h : μ = τ
    · subst h
      exact ⟨1, fun G _ => Commute.one_left G, fun W _ x hx => hx, fun y _ => rfl, hx⟩
    · refine ⟨(τ - μ)⁻¹ • (F - μ • 1), fun G hG => ?_, fun W hW y hy => ?_, fun y hy => ?_, ?_⟩
      · exact (hG.sub_left ((Commute.one_left G).smul_left μ)).smul_left _
      · simpa using W.smul_mem _ (W.sub_mem (hW y hy) (W.smul_mem μ hy))
      · have h' : τ - μ ≠ 0 := sub_ne_zero.2 (Ne.symm h)
        simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hy, ← sub_smul, smul_smul,
          inv_mul_cancel₀ h', one_smul]
      · simp [hx]
  | zero => exact ⟨1, fun G _ => Commute.one_left G, fun W _ x hx => hx, fun y _ => rfl, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨P, hP1, hP2, hP3, hP4⟩ := ihx
    obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := ihy
    have hPQ : Commute P Q := hP1 Q (hQ1 F (Commute.refl F)).symm
    refine ⟨P * Q, fun G hG => (hP1 G hG).mul_left (hQ1 G hG), fun W hW z hz => hP2 W hW _ (hQ2 W hW z hz),
      fun z hz => ?_, ?_⟩
    · rw [Module.End.mul_apply, hQ3 z hz, hP3 z hz]
    · have h1 : (P * Q) x = P x := by rw [hPQ.eq, Module.End.mul_apply, hQ3 _ hP4]
      have h2 : (P * Q) y = Q y := by rw [Module.End.mul_apply, hP3 _ hQ4]
      rw [map_add (f := _), h1, h2, map_add (f := _), hP4, hQ4, smul_add]

theorem mem_iSup_eigenspace {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : Module.End ℂ V)
    (hT : T.IsSymmetric) (S : Submodule ℂ V) [FiniteDimensional ℂ S] (hS : ∀ v ∈ S, T v ∈ S) (x : V) (hx : x ∈ S) :
    x ∈ ⨆ μ : ℂ, T.eigenspace μ := by
  have hs : (T.restrict hS).IsSymmetric := hT.restrict_invariant hS
  have htop : (⨆ μ : ℂ, Module.End.eigenspace (T.restrict hS) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hs.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hle : ((⨆ μ : ℂ, Module.End.eigenspace (T.restrict hS) μ).map S.subtype) ≤ ⨆ μ : ℂ, T.eigenspace μ := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun μ => ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Module.End.mem_eigenspace_iff.1 hy
    rw [Module.End.mem_eigenspace_iff]
    exact congrArg Subtype.val hy'
  exact hle ⟨⟨x, hx⟩, by rw [htop]; trivial, rfl⟩

theorem Ft_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (x : Cn n V) (A : Finset (Pos n)) :
    Ft ε E c x A = E c c (x A) + (wt (A.filter (cpt ε)) c : ℂ) • x A := rfl

theorem chain_mem_iSup {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (h : ∀ v : V, v ∈ ⨆ μ : ℂ, (E c c).eigenspace μ)
    (t : Cn n V) : t ∈ ⨆ μ : ℂ, (Ft ε E c).eigenspace μ := by
  classical
  rw [← Finset.univ_sum_single t]
  refine Submodule.sum_mem _ fun A _ => ?_
  have hle : (⨆ μ : ℂ, (E c c).eigenspace μ).map (LinearMap.single ℂ (fun _ : Finset (Pos n) => V) A) ≤
      ⨆ μ : ℂ, (Ft ε E c).eigenspace μ := by
    rw [Submodule.map_iSup]
    refine iSup_le fun μ => le_trans ?_ (le_iSup _ (μ + (wt (A.filter (cpt ε)) c : ℂ)))
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Module.End.mem_eigenspace_iff.1 hy
    rw [Module.End.mem_eigenspace_iff]
    funext B
    rw [Ft_apply]
    by_cases hB : B = A
    · subst hB
      simp [hy', add_smul]
    · simp [Pi.single_eq_of_ne hB]
  exact hle ⟨t A, h _, rfl⟩

theorem Ft_commute {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε₀ ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hE : KRel ε E) (c d : Fin n) : Commute (Ft ε₀ E c) (Ft ε₀ E d) := by
  have h : E c c * E d d = E d d * E c c := by
    have := hE c c d d rfl rfl
    by_cases hcd : c = d
    · subst hcd; rfl
    · rw [if_neg hcd, if_neg (Ne.symm hcd), sub_zero, sub_eq_zero] at this
      exact this
  refine LinearMap.ext fun x => funext fun A => ?_
  have h' : E c c (E d d (x A)) = E d d (E c c (x A)) := LinearMap.congr_fun h (x A)
  simp only [Module.End.mul_apply, Ft_apply, map_add (f := _), map_smul, h', smul_add, smul_smul,
    mul_comm (wt (A.filter (cpt ε₀)) c : ℂ)]
  abel

theorem wtProj : CompanionTheory.D.LK.WtProj := by
  intro n ε₀ ε V _ _ E hE hU hL D hD τ t ht
  have hdiag : ∀ c (x : Cn n V), x ∈ ⨆ μ : ℂ, (Ft ε₀ E c).eigenspace μ := fun c =>
    chain_mem_iSup ε₀ E c fun v => by
      obtain ⟨S, hS, hst, hv⟩ := hL v
      exact mem_iSup_eigenspace (E c c) (fun x y => hU c c rfl x y) S (hst c c rfl) v hv
  let W : Submodule ℂ (Cn n V) :=
    { carrier := {x | ∀ A, t A = 0 → x A = 0}
      add_mem' := fun {a b} ha hb A hA => by simp [ha A hA, hb A hA]
      zero_mem' := fun A _ => rfl
      smul_mem' := fun c a ha A hA => by simp [ha A hA] }
  have hW : ∀ c, ∀ x ∈ W, Ft ε₀ E c x ∈ W := fun c x hx A hA => by
    rw [Ft_apply, hx A hA]; simp
  have key : ∀ s : Finset (Fin n), ∃ t' : Cn n V, (∀ c ∈ s, Ft ε₀ E c t' = (τ c : ℂ) • t') ∧ D t' = D t ∧
      t' ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨t, by simp, rfl, fun A hA => hA⟩
    | insert c s _ ih =>
      obtain ⟨u, hu1, hu2, hu3⟩ := ih
      obtain ⟨P, hP1, hP2, hP3, hP4⟩ := exists_proj (Ft ε₀ E c) (τ c) u (hdiag c u)
      refine ⟨P u, fun d hd => ?_, ?_, hP2 W (hW c) u hu3⟩
      · rcases Finset.mem_insert.1 hd with rfl | hd
        · exact hP4
        · have := LinearMap.congr_fun (hP1 _ (Ft_commute ε₀ ε E hE c d)).eq u
          simp only [Module.End.mul_apply] at this
          rw [← this, hu1 d hd, map_smul]
      · have := LinearMap.congr_fun (hP1 _ (hD c)).eq u
        simp only [Module.End.mul_apply] at this
        rw [← this, hu2, hP3 _ (ht c)]
  obtain ⟨t', h1, h2, h3⟩ := key univ
  exact ⟨t', fun c => h1 c (mem_univ c), h2, h3⟩

end GlobalTheory.CompanionTheory.LKWtProj
end
end
