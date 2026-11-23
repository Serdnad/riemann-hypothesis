module

public import Formalism.SatakeDualWeyl.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem cT_map {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) {m p : Type} (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem base_change_mem_holds : Formalism.UG.BCMem := by
  intro A B _ _ n _ _ σ σ' φ h J g hg
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) =
    J.map φ
  have e : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ := rfl
  rw [e, cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem rational_points_le_holds : Formalism.UG.RatPtsLe := by
  intro F E _ _ _ n _ _ σ J R _ _ x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hc : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE (F := F) R) := by
    ext e
    simp [inclE, sigR, Algebra.TensorProduct.map_tmul]
  exact base_change_mem_holds E (E ⊗[F] R) n (σ : E →+* E) (sigR σ R) (inclE (F := F) R) hc J g hg

end Formalism.UG.P
end
end

section

noncomputable section

open Matrix

namespace Formalism.UG.P

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem split_mat_ext {M N : Matrix n n (R × R)} (h1 : M.map Prod.fst = N.map Prod.fst)
    (h2 : M.map Prod.snd = N.map Prod.snd) : M = N := by
  ext i j
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

theorem split_map_fst_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.fst = M.map Prod.fst * N.map Prod.fst := by
  ext i j
  simp [Matrix.mul_apply, Prod.fst_sum]

theorem split_map_snd_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.snd = M.map Prod.snd * N.map Prod.snd := by
  ext i j
  simp [Matrix.mul_apply, Prod.snd_sum]

theorem split_cT_fst (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.fst = (g.map Prod.snd)ᵀ := by
  ext i j
  simp [cT, swapR, Matrix.map_apply, Matrix.transpose_apply]

theorem split_cT_snd (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.snd = (g.map Prod.fst)ᵀ := by
  ext i j
  simp [cT, swapR, Matrix.map_apply, Matrix.transpose_apply]

theorem splitJ_fst (J₁ : Matrix n n R) : (splitJ J₁).map Prod.fst = J₁ := by
  ext i j
  simp [splitJ, Matrix.map_apply]

theorem splitJ_snd (J₁ : Matrix n n R) : (splitJ J₁).map Prod.snd = J₁ᵀ := by
  ext i j
  simp [splitJ, Matrix.map_apply, Matrix.transpose_apply]

theorem split_mem_iff (J₁ : Matrix n n R) (g : GL n (R × R)) :
    g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁) ↔
      ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * (g : Matrix n n (R × R)).map Prod.fst
        = J₁ := by
  constructor
  · intro h
    have h' := congrArg (fun M : Matrix n n (R × R) => M.map Prod.fst)
      (show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁ from h)
    simpa only [split_map_fst_mul, split_cT_fst, splitJ_fst] using h'
  · intro h
    show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁
    apply split_mat_ext
    · rw [split_map_fst_mul, split_map_fst_mul, split_cT_fst, splitJ_fst, h]
    · rw [split_map_snd_mul, split_map_snd_mul, split_cT_snd, splitJ_snd]
      have h' := congrArg Matrix.transpose h
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h'
      rw [← Matrix.mul_assoc] at h'
      exact h'

theorem split_conj_mul (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) {P Q : Matrix n n R}
    (hPQ : P * Q = 1) : (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = 1 := by
  have h1 : J₁⁻¹ * J₁ = 1 := Matrix.nonsing_inv_mul _ hJ
  have h2 : J₁ * J₁⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  calc (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = J₁ * (P * (J₁⁻¹ * J₁) * Q) * J₁⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, hPQ, Matrix.mul_one, h2]

def pairMat (X Y : Matrix n n R) : Matrix n n (R × R) := fun i j => (X i j, Y i j)

theorem pairMat_fst (X Y : Matrix n n R) : (pairMat X Y).map Prod.fst = X := by
  ext i j
  rfl

theorem pairMat_snd (X Y : Matrix n n R) : (pairMat X Y).map Prod.snd = Y := by
  ext i j
  rfl

theorem pairMat_mul_eq_one {X Y X' Y' : Matrix n n R} (h1 : X * X' = 1) (h2 : Y * Y' = 1) :
    pairMat X Y * pairMat X' Y' = 1 := by
  apply split_mat_ext
  · rw [split_map_fst_mul, pairMat_fst, pairMat_fst, h1]
    exact (Matrix.map_one _ rfl rfl).symm
  · rw [split_map_snd_mul, pairMat_snd, pairMat_snd, h2]
    exact (Matrix.map_one _ rfl rfl).symm

theorem split_injective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (g g' : GL n (R × R))
    (hg : g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁)) (hg' : g' ∈ Formalism.UG.UJ (swapR R) (splitJ J₁))
    (h : (g : Matrix n n (R × R)).map Prod.fst = (g' : Matrix n n (R × R)).map Prod.fst) :
    g = g' := by
  have hF : (g : Matrix n n (R × R)).map Prod.fst * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst = 1 := by
    rw [← split_map_fst_mul, Units.mul_inv]
    exact Matrix.map_one _ rfl rfl
  have e1 := (split_mem_iff J₁ g).mp hg
  have e2 := (split_mem_iff J₁ g').mp hg'
  rw [← h] at e2
  have k1 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1]
  have k2 : ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e2]
  have k3 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ := by
    have h3 := congrArg (fun M : Matrix n n R => M * J₁⁻¹) (k1.trans k2.symm)
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one] using h3
  have k4 := congrArg Matrix.transpose k3
  rw [Matrix.transpose_transpose, Matrix.transpose_transpose] at k4
  exact Units.ext (split_mat_ext h k4)

theorem split_surjective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (h : GL n R) :
    ∃ g : GL n (R × R), g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁) ∧ bc (RingHom.fst R R) g = h := by
  have hS : (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ * (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ (Units.mul_inv h), Matrix.transpose_one]
  have hSi : (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ * (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ (Units.inv_mul h), Matrix.transpose_one]
  refine ⟨⟨pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ,
    pairMat ((h⁻¹ : GL n R) : Matrix n n R) (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ,
    pairMat_mul_eq_one (Units.mul_inv h) hS, pairMat_mul_eq_one (Units.inv_mul h) hSi⟩, ?_, ?_⟩
  · apply (split_mem_iff J₁ _).mpr
    show ((pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ).map Prod.snd)ᵀ * J₁ *
      (pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ).map Prod.fst = J₁
    rw [pairMat_snd, pairMat_fst, Matrix.transpose_transpose]
    calc J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹ * J₁ * (h : Matrix n n R)
        = J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * (J₁⁻¹ * J₁) * (h : Matrix n n R) := by
          simp only [Matrix.mul_assoc]
      _ = J₁ := by
          rw [Matrix.nonsing_inv_mul _ hJ, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  · exact Units.ext (pairMat_fst (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ)

theorem split_unitary_group_iso : Formalism.UG.SplitIso := by
  intro R _ n _ _ J₁ hJ
  refine ⟨MulEquiv.ofBijective ((bc (RingHom.fst R R)).comp (Formalism.UG.UJ (swapR R) (splitJ J₁)).subtype) ⟨?_, ?_⟩,
    fun g => rfl⟩
  · intro a b hab
    apply Subtype.ext
    apply split_injective J₁ hJ a b a.2 b.2
    exact congrArg (fun u : GL n R => (u : Matrix n n R)) hab
  · intro h
    obtain ⟨g, hg, he⟩ := split_surjective J₁ hJ h
    exact ⟨⟨g, hg⟩, he⟩

end Formalism.UG.P
end
end

section

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem transport_cT_map {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) {m p : Type} (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem transport_bc_mem {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n]
    [DecidableEq n] (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  rw [transport_cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem transport_symm_comp {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A ≃+* B) (h : (φ : A →+* B).comp σ = σ'.comp φ) :
    (φ.symm : B →+* A).comp σ' = σ.comp φ.symm := by
  ext x
  have h1 := RingHom.congr_fun h (φ.symm x)
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h1 ⊢
  rw [← h1, RingEquiv.symm_apply_apply]

theorem unitary_group_transport : Formalism.UG.UJTransport := by
  intro A B _ _ n _ _ σ σ' φ h J
  have hs := transport_symm_comp σ σ' φ h
  refine ⟨{ toFun := fun g => ⟨bc (φ : A →+* B) g, transport_bc_mem σ σ' φ h J g g.2⟩
            invFun := fun g => ⟨bc (φ.symm : B →+* A) g, by
              have hm := transport_bc_mem σ' σ (φ.symm : B →+* A) hs (J.map φ) g g.2
              have hJ : (J.map φ).map (φ.symm : B →+* A) = J := by ext i j; simp
              rwa [hJ] at hm⟩
            left_inv := fun g => by
              apply Subtype.ext; apply Units.ext; ext i j; simp [bc]
            right_inv := fun g => by
              apply Subtype.ext; apply Units.ext; ext i j; simp [bc]
            map_mul' := fun a b => by
              apply Subtype.ext; simp }, fun g => rfl⟩

theorem split_group_points : Formalism.UG.SplitPts := by
  intro F E _ _ _ n _ _ σ J R _ _ φ hφ
  have hc : (φ : E ⊗[F] R →+* R × R).comp (sigR σ R) = (swapR R).comp φ := RingHom.ext hφ
  obtain ⟨e, he⟩ := unitary_group_transport (E ⊗[F] R) (R × R) n (sigR σ R) (swapR R) φ hc
    (J.map (inclE (F := F) R))
  exact ⟨e, he⟩

end Formalism.UG.P
end
end

section

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

section Rep

variable {G : Type} [Group G] (Γ K : Subgroup G)

theorem mem_AMFK_iff {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρK : Representation k K W) (f : G → W) :
    f ∈ AMFK k Γ K ρK ↔ ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ρK κ⁻¹ (f g) := Iff.rfl

theorem exists_rep (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c) (g : G) :
    ∃ p : Γ × K, g = (p.1 : G) * s (DoubleCoset.mk Γ K g) * (p.2 : G) := by
  have h := (@DoubleCoset.eq _ _ Γ K (s (DoubleCoset.mk Γ K g)) g).1 (hs _)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

end Rep

theorem automorphic_forms_level_finite_holds : Formalism.UG.AMFKFinite := by
  intro G _ Γ K k _ _ W _ _ _ ρK hfin
  have hsurj : ∀ c : ClassSet Γ K, ∃ g : G, DoubleCoset.mk Γ K g = c := by
    intro c
    obtain ⟨g, hg⟩ := Quotient.exists_rep c
    exact ⟨g, hg⟩
  let s : ClassSet Γ K → G := fun c => (hsurj c).choose
  have hs : ∀ c, DoubleCoset.mk Γ K (s c) = c := fun c => (hsurj c).choose_spec
  let L : AMFK k Γ K ρK →ₗ[k] (ClassSet Γ K → W) :=
    LinearMap.pi fun c => (LinearMap.proj (s c)).comp (AMFK k Γ K ρK).subtype
  have hinj : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext x
    obtain ⟨p, hp⟩ := exists_rep Γ K s hs x
    have hf := (mem_AMFK_iff Γ K ρK (f : G → W)).1 f.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hg := (mem_AMFK_iff Γ K ρK (g : G → W)).1 g.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hfc := congrFun hfg (DoubleCoset.mk Γ K x)
    change (f : G → W) (s (DoubleCoset.mk Γ K x)) = (g : G → W) (s (DoubleCoset.mk Γ K x)) at hfc
    rw [← hp] at hf hg
    rw [hf, hg, hfc]
  exact Module.Finite.of_injective L hinj

end Formalism.UG.P
end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

section Gen

variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_coe_bc (f : R →+* A) (u : GL n R) :
    ((bc (n := n) f u : GL n A) : Matrix n n A) = (u : Matrix n n R).map f := by
  rfl

theorem levelvsplit_mem_range_iff (f : R →+* A) (hf : Function.Injective f) (g : GL n A) :
    g ∈ (bc (n := n) f).range ↔
      (∀ i j, (g : Matrix n n A) i j ∈ Set.range f) ∧
        ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ Set.range f := by
  constructor
  · intro hg
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hg
    refine ⟨fun i j => ⟨(u : Matrix n n R) i j, rfl⟩, fun i j => ⟨((u⁻¹ : GL n R) : Matrix n n R) i j, ?_⟩⟩
    rw [← map_inv (bc (n := n) f) u]
    rfl
  · rintro ⟨h1, h2⟩
    choose M hM using h1
    choose N hN using h2
    have hinj : Function.Injective (f.mapMatrix : Matrix n n R →+* Matrix n n A) := by
      intro X Y h
      ext i j
      have h' := congrArg (fun Z : Matrix n n A => Z i j) h
      exact hf h'
    have hMg : f.mapMatrix (Matrix.of M) = (g : Matrix n n A) := by
      ext i j
      exact hM i j
    have hNg : f.mapMatrix (Matrix.of N) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j
      exact hN i j
    have e1 : Matrix.of M * Matrix.of N = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.mul_inv])
    have e2 : Matrix.of N * Matrix.of M = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.inv_mul])
    exact MonoidHom.mem_range.mpr ⟨⟨Matrix.of M, Matrix.of N, e1, e2⟩, Units.ext hMg⟩

end Gen

section Split

variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_unitary (τ : B →+* B) (φ : B ≃+* K × K)
    (hτ : ∀ x, φ (τ x) = swapR K (φ x)) (J' : Matrix n n B) (h : GL n B) (hh : h ∈ UJ τ J') :
    ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ *
        J'.map ((RingHom.fst K K).comp φ.toRingHom) *
        (h : Matrix n n B).map ((RingHom.fst K K).comp φ.toRingHom) =
      J'.map ((RingHom.fst K K).comp φ.toRingHom) := by
  have hh' : Formalism.UG.cT τ (h : Matrix n n B) * J' * (h : Matrix n n B) = J' := hh
  have key : (Formalism.UG.cT τ (h : Matrix n n B)).map ((RingHom.fst K K).comp φ.toRingHom) =
      ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ := by
    ext i j
    simp [Formalism.UG.cT, hτ, Formalism.UG.swapR]
  have h2 := congrArg (fun M : Matrix n n B => M.map ((RingHom.fst K K).comp φ.toRingHom)) hh'
  simp only [Matrix.map_mul] at h2
  rw [key] at h2
  exact h2

theorem levelvsplit_solve (A Ainv P1 P1i P2 : Matrix n n K) (hA : A * Ainv = 1)
    (hP : P1 * P1i = 1) (hrel : P2ᵀ * A * P1 = A) : P2 = (A * P1i * Ainv)ᵀ := by
  have h1 : P2ᵀ * A = A * P1i := by
    calc P2ᵀ * A = P2ᵀ * A * (P1 * P1i) := by rw [hP, Matrix.mul_one]
      _ = P2ᵀ * A * P1 * P1i := by simp only [Matrix.mul_assoc]
      _ = A * P1i := by rw [hrel]
  have h2 : P2ᵀ = A * P1i * Ainv := by
    calc P2ᵀ = P2ᵀ * (A * Ainv) := by rw [hA, Matrix.mul_one]
      _ = P2ᵀ * A * Ainv := by rw [Matrix.mul_assoc]
      _ = A * P1i * Ainv := by rw [h1]
  rw [← h2, Matrix.transpose_transpose]

end Split

end Formalism.UG.P
end
end
