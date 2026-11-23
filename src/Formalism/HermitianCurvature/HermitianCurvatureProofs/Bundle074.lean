module

public import Formalism.HermitianCurvature.Bundle009
public import Mathlib.Algebra.Lie.Sl2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
public import Formalism.HermitianCurvature.StatementQr
public import Mathlib.LinearAlgebra.Vandermonde
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoRatioPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

section

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CommonEigenvectors

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem eig_in [FiniteDimensional ℂ V] (T : Module.End ℂ V) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hT : ∀ x ∈ G, T x ∈ G) : ∃ (μ : ℂ) (x : V), x ∈ G ∧ x ≠ 0 ∧ T x = μ • x := by
  haveI : Nontrivial G := Submodule.nontrivial_iff_ne_bot.2 hG
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T.restrict hT)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, x, x.2, fun h => hx.2 (Subtype.ext h), ?_⟩
  have h1 := Module.End.mem_eigenspace_iff.1 hx.1
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem common [FiniteDimensional ℂ V] {ι : Type} [DecidableEq ι] (D : ι → Module.End ℂ V)
    (hc : ∀ a b, D a * D b = D b * D a) (s : Finset ι) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hst : ∀ a, ∀ x ∈ G, D a x ∈ G) :
    ∃ (G' : Submodule ℂ V) (ν : ι → ℂ), G' ≤ G ∧ G' ≠ ⊥ ∧ (∀ a, ∀ x ∈ G', D a x ∈ G') ∧
      ∀ a ∈ s, ∀ x ∈ G', D a x = ν a • x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨G, 0, le_rfl, hG, hst, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨G₁, ν, h1, h2, h3, h4⟩ := ih
    obtain ⟨μ, x, hx1, hx2, hx3⟩ := eig_in (D a) G₁ h2 (h3 a)
    refine ⟨G₁ ⊓ LinearMap.ker (D a - μ • 1), Function.update ν a μ, le_trans inf_le_left h1, ?_, ?_, ?_⟩
    · intro hbot
      apply hx2
      have hm : x ∈ G₁ ⊓ LinearMap.ker (D a - μ • 1) :=
        Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (by simp [hx3])⟩
      rw [hbot] at hm
      simpa using hm
    · intro c y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      have hcomm : D a (D c y) = D c (D a y) := by
        have := congrArg (fun T => T y) (hc a c)
        simpa using this
      exact Submodule.mem_inf.2 ⟨h3 c y hy1, LinearMap.mem_ker.2 (by simp [hcomm, hy2'])⟩
    · intro b hb y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      rcases Finset.mem_insert.1 hb with rfl | hb
      · simp [hy2']
      · have hba : b ≠ a := fun h => ha (h ▸ hb)
        simp [Function.update_apply, hba, h4 b hb y hy1]

def hop {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • E c c

theorem diag_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c a b : Fin n) (x : V) :
    E c c (E a b x) = E a b (E c c x) + ((if c = a then E a b x else 0) - (if b = c then E a b x else 0)) := by
  have h : E c c (E a b x) - E a b (E c c x) = ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x :=
    congrArg (fun T => T x) (hE c c a b)
  rw [sub_eq_iff_eq_add'] at h
  rw [h, LinearMap.sub_apply]
  congr 1
  split_ifs <;> subst_vars <;> simp

theorem hop_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) (x : V) :
    hop E (E a b x) = E a b (hop E x) + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ)) • E a b x := by
  unfold hop

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, diag_move hE, smul_add, smul_sub,
  smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
  Finset.mem_univ, if_true]
  rw [← sub_smul]
  congr 2
  ring

theorem hop_weight {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {θ : Fin n → ℂ} {x : V}
    (hx : ∀ a, E a a x = θ a • x) :
    hop E x = (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c) • x := by
  unfold hop
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.smul_apply, hx, smul_smul]

theorem hval_re {n : ℕ} (θ : Fin n → ℂ) :
    (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c).re = hval θ := by
  unfold hval
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [Complex.mul_re]

end Formalism.FourierDecayAlt.P.CommonEigenvectors

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors

theorem exists_singular_maximal_vector : Qr.ExistsSingMax := by
  intro V _ _ _ n E hE S hS hS0
  have hcomm : ∀ a b : Fin n, E a a * E b b = E b b * E a a := by
    intro a b
    have h := hE a a b b
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S := by
    intro a b x hx
    exact hS a b x hx
  obtain ⟨G', ν0, hG'S, hG'0, -, hG'ν⟩ :=
    common (fun a => E a a) hcomm Finset.univ S hS0 (fun a => hstab a a)
  obtain ⟨x0, hx0G, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG'0
  let W : Set (Fin n → ℂ) := {θ | ∃ x ∈ S, x ≠ 0 ∧ ∀ a, E a a x = θ a • x}
  have hWne : W.Nonempty := ⟨ν0, x0, hG'S hx0G, hx00, fun a => hG'ν a (Finset.mem_univ a) x0 hx0G⟩
  have hWfin : W.Finite := by
    refine (Set.Finite.pi (t := fun a => {μ | (E a a).HasEigenvalue μ})
      fun a => Module.End.finite_hasEigenvalue (E a a)).subset ?_
    rintro θ ⟨x, -, hx0, hx⟩
    exact Set.mem_univ_pi.2 fun a =>
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hx a), hx0⟩
  obtain ⟨ν, ⟨v, hvS, hv0, hv⟩, hmax⟩ := Set.exists_max_image W hval hWfin hWne
  refine ⟨ν, v, hvS, hv0, ⟨hv, fun a b hab => ?_⟩, fun θ x hxS hx0 hx => hmax θ ⟨x, hxS, hx0, hx⟩⟩
  by_contra hy
  set y := E a b v with hydef
  have hyS : y ∈ S := hstab a b v hvS
  let θ' : Fin n → ℂ := fun c => ν c + ((if c = a then 1 else 0) - (if b = c then 1 else 0))
  have hy' : ∀ c, E c c y = θ' c • y := by
    intro c
    rw [hydef, diag_move hE, hv c, map_smul]
    simp only [θ', add_smul, sub_smul, ite_smul, one_smul, zero_smul]
  have hle := hmax θ' ⟨y, hyS, hy, hy'⟩
  have k1 := hop_weight hy'
  have k2 := hop_move hE a b v
  rw [hop_weight hv, map_smul, ← hydef, ← add_smul, k1] at k2
  have k3 := smul_left_injective ℂ hy k2
  have hv' : hval θ' = hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [← hval_re, ← hval_re, k3]
    simp
  have hba : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by
    have := Fin.lt_iff_val_lt_val.1 hab
    exact_mod_cast this
  linarith

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem singular_dominant : Qr.SingDom := by
  intro V _ _ _ n E ν v hE hv hv0 a b hab
  obtain ⟨hd, hr⟩ := hv
  have hab' : a ≠ b := ne_of_lt hab
  by_cases h0 : E a a - E b b = 0
  · refine ⟨0, ?_⟩
    have h1 : (E a a - E b b) v = 0 := by rw [h0]; rfl
    rw [LinearMap.sub_apply, hd, hd, ← sub_smul] at h1
    simpa [hv0] using h1
  · have e0 := hE a b b a
    have e1 := hE a a a b
    have e2 := hE b b a b
    have e3 := hE a a b a
    have e4 := hE b b b a
    simp [hab', hab'.symm] at e0 e1 e2 e3 e4
    have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
      { h_ne_zero := h0
        lie_e_f := by rw [Ring.lie_def, e0]
        lie_h_e_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E a b - E a b * (E a a - E b b)
              = (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
            _ = 2 • E a b := by rw [e1, e2]; abel
        lie_h_f_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E b a - E b a * (E a a - E b b)
              = (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
            _ = -(2 • E b a) := by rw [e3, e4]; abel }
    have pv : t.HasPrimitiveVectorWith v (ν a - ν b) :=
      { ne_zero := hv0
        lie_h := by
          show (E a a - E b b) v = (ν a - ν b) • v
          rw [LinearMap.sub_apply, hd, hd, sub_smul]
        lie_e := by
          show E a b v = 0
          exact hr a b hab }
    exact pv.exists_nat

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def QTop : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (h : ℂ),
    ∃ d : ℕ → A, (∀ Y : ℂ, qminor E id id (Y + h) = ∑ j ∈ Finset.range (n + 1), Y ^ j • d j) ∧
      (1 ≤ n → d (n - 1) = ∑ a, E a a + algebraMap ℂ A ((n : ℂ) * h - (n : ℂ) * ((n : ℂ) - 1) / 2))

theorem interp {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ)
    (hW : W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1) (p : ℂ → V) (a : ℕ → V)
    (ha : ∀ Y, p Y = ∑ j ∈ Finset.range N, Y ^ j • a j) (j : Fin N) :
    ∑ i : Fin N, W j i • p ((i : ℕ) : ℂ) = a j := by
  have key : ∀ l : Fin N, ∑ i : Fin N, W j i * ((i : ℕ) : ℂ) ^ (l : ℕ) = if j = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hW j) l
    simpa [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] using h
  simp_rw [ha, Finset.sum_range, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key, ite_smul, one_smul, zero_smul]
  simp

theorem vdm_inv (N : ℕ) : ∃ W : Matrix (Fin N) (Fin N) ℂ,
    W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1 := by
  refine ⟨(Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)))⁻¹, Matrix.nonsing_inv_mul _ ?_⟩
  rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  exact Fin.ext (Nat.cast_injective h)

theorem pt_poly (hQ : QTop) {k r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (D : Set (Mx k r)) (hD : IsOpen D) (f : Mx k r → V) (hf : SmoothLev k r (Fin.last r) D f)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    ∃ a : ℕ → V, (∀ Y : ℂ, capL k r (Fin.last r) (uC k r (Fin.last r) Y) f g =
        ∑ j ∈ Finset.range (mdim k r (Fin.last r) + 1), Y ^ j • a j) ∧
      a (mdim k r (Fin.last r) - 1) = ∑ b : Fin (mdim k r (Fin.last r)),
        EH k r (posL k r (Fin.last r) b) (posL k r (Fin.last r) b) f g := by
  obtain ⟨d, hd, htop⟩ := hQ (Module.End ℂ (SV k r (Fin.last r) D V)) (mdim k r (Fin.last r))
    (EV k r (Fin.last r) D V) (((mdim k r (Fin.last r) : ℂ) - 1) / 2)
  refine ⟨fun j => (d j (mkV hD f hf)).1 g, fun Y => ?_, ?_⟩
  · have h1 := (OperatorRepresentations.rep_qminor (E := V) hD (id : Fin (mdim k r (Fin.last r)) → Fin (mdim k r (Fin.last r))) id
      (uC k r (Fin.last r) Y)).mkV hD hf hg
    simp only [Function.comp_id] at h1
    have e : uC k r (Fin.last r) Y = Y + ((mdim k r (Fin.last r) : ℂ) - 1) / 2 := rfl
    unfold capL
    rw [← h1, e, hd Y, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  · have hn1 : 1 ≤ mdim k r (Fin.last r) := by simp [mdim]
    show (d (mdim k r (Fin.last r) - 1) (mkV hD f hf)).1 g = _
    rw [htop hn1]
    have e0 : ((mdim k r (Fin.last r) : ℂ) * (((mdim k r (Fin.last r) : ℂ) - 1) / 2) -
        (mdim k r (Fin.last r) : ℂ) * ((mdim k r (Fin.last r) : ℂ) - 1) / 2) = 0 := by ring
    rw [e0, map_zero, add_zero, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => (OperatorRepresentations.rep_EV (E := V) hD b b).mkV hD hf hg

theorem mdim_last (k r : ℕ) : mdim k r (Fin.last r) = k + 1 := by
  simp [Q.mdim]

theorem gTRTopAct_of_cut (hQ : QTop) : GTRTopAct := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl hk X
  obtain ⟨W, hW⟩ := vdm_inv (P.k + 2)

  have hpt : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z',
      ∃ a : ℕ → (Wq →L[ℂ] Wp), (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) ∧
        a P.k = ∑ b : Fin (mdim P.k P.r (Fin.last P.r)),
          EH P.k P.r (posL P.k P.r (Fin.last P.r) b) (posL P.k P.r (Fin.last P.r) b)
            ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2 := by
    intro Φ x hx
    have hmem := Φ.2
    obtain ⟨_, hs, _⟩ := hmem
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x hx
    set D : Set (Mx P.k P.r) := {g | (x.1, g) ∈ U} with hDdef
    have hc : ContDiff ℝ ∞ (fun g : Mx P.k P.r => (x.1, g)) := contDiff_prodMk_right x.1
    have hD : IsOpen D := hU.preimage hc.continuous
    have hf : SmoothLev P.k P.r (Fin.last P.r) D ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) := by
      intro g₀ hg₀
      refine ⟨D, fun g => F (x.1, g), hD, hg₀.2, ?_, fun g hgD hgG => hΦ (x.1, g) hgD hgG⟩
      exact hF.comp hc.contDiffOn (fun g hg => hg)
    have hg : x.2 ∈ Glev P.k P.r (Fin.last P.r) ∩ D := ⟨hx.2.1, by simpa [hDdef] using hxU⟩
    obtain ⟨a, ha, htop⟩ := pt_poly hQ D hD _ hf hg
    have hm : mdim P.k P.r (Fin.last P.r) + 1 = P.k + 2 := by rw [mdim_last]
    have hm1 : mdim P.k P.r (Fin.last P.r) - 1 = P.k := by rw [mdim_last]; rfl
    refine ⟨a, fun Y => ?_, ?_⟩
    · rw [X.t_apply Y 0 0 Φ x hx, ← hm]
      exact ha Y
    · rw [← htop, hm1]

  let c : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π') := fun j =>
    if h : j < P.k + 2 then ∑ i : Fin (P.k + 2), W ⟨j, h⟩ i • X.t ((i : ℕ) : ℂ) 0 0 else 0
  have hval : ∀ (T : Module.End ℂ (RadSp P.k P.r z z' π π')) (Φ : RadSp P.k P.r z z' π π') x,
      x ∉ DomR P.k P.r z z' → ((T Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := by
    intro T Φ x hx
    have hmem := (T Φ).2
    obtain ⟨h0, _, _⟩ := hmem
    exact h0 x hx
  have hc : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z', ∀ (a : ℕ → (Wq →L[ℂ] Wp)),
      (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) →
      ∀ j ∈ Finset.range (P.k + 2), ((c j Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = a j := by
    intro Φ x hx a ha j hj
    have hj' : j < P.k + 2 := Finset.mem_range.1 hj
    have e1 : c j = ∑ i : Fin (P.k + 2), W ⟨j, hj'⟩ i • X.t ((i : ℕ) : ℂ) 0 0 := dif_pos hj'
    rw [e1, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    exact interp (P.k + 2) W hW (fun Y => ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      a ha ⟨j, hj'⟩
  refine ⟨c, fun Y => ?_, 0, fun Φ x hx => ?_⟩
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    funext c0 g
    by_cases hx : (c0, g) ∈ DomR P.k P.r z z'
    · obtain ⟨a, ha, -⟩ := hpt Φ (c0, g) hx
      have hL := ha Y
      simp only at hL
      rw [hL, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
      congr 1
      exact (hc Φ (c0, g) hx a ha j hj).symm
    · have h1 := hval (X.t Y 0 0) Φ (c0, g) hx
      have h2 := hval (∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) Φ (c0, g) hx
      simp only at h1 h2
      rw [h1, h2]
  · obtain ⟨a, ha, htop⟩ := hpt Φ x hx
    rw [hc Φ x hx a ha P.k (Finset.mem_range.2 (by omega)), htop]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

def GLRight : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Gauge.IsFrameB P Bs e →
    (∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr →
    ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ (Y : ℝ) (X' : Wq →L[ℂ] Wp),
      (∀ v, X' v = X (Q.capRep P.k P.r Bs.π' Fr ((Y : ℂ) + ((P.k : ℂ) - 2) / 2) v)) →
      ∀ ρ : M.Ty P, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X') = M.xC P ρ (Y : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X)

def GLLeft : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [Bs.z, SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ] Fr →
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) ∧
      ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ (w : ℂ) (v : Wq),
        Q.capRep P.k P.r Bs.π Fr w (X v) =
          X (Q.capRep P.k P.r Bs.π' (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) w v)

def GaugeLinesOfCut : Prop := GLRight → GLLeft → GaugeLines

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

section

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}

theorem GermD.germLoc_tail (hG : GermD s β ε Y ut bt SS) (Gk : ι × ℂ → ι × ℂ → ℂ)
    (hGk : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      Gk (h, x) (h', x') = gramL volume (Uc s ut) (Uc s ut) (h, x) (h', x'))
    (hatB : ℂ → ι → ι → ℂ) (hN : ∀ σ : ℂ, ∀ h ∈ Y, ∀ h' ∈ Y, Nhat s β bt σ h h' = hatB σ h h') :
    (∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z => ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ)) ∧
    ∃ Pua Paa : ι × ℂ → ι × ℂ → ℂ,
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) Gk Pua Paa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖Paa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
        Tendsto (fun x => Paa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB σ h h')) ∧
        Tendsto (fun x => Pua (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB σ h h')) ∧
        Tendsto (fun x => conj (Pua (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hatB σ h h')) := by
  obtain ⟨h0, h1, h2, h3⟩ := hG.propG
  refine ⟨fun h hh h' hh' => integrable_inner_of_memLp (h0 h hh).1 (h0 h' hh').1,
    gramL volume (Uc s ut) (Ac s β ε bt), gramL volume (Ac s β ε bt) (Ac s β ε bt),
    fun Xs hXs => ?_, h2, fun h hh h' hh' σ => ?_⟩
  · have hb := h1 Xs hXs
    unfold KB.BlockPSD TB.PSDOn at hb ⊢
    open scoped ComplexOrder in
    refine (congrArg Matrix.PosSemidef ?_).mpr hb
    ext i j
    obtain ⟨x, hx⟩ := i
    obtain ⟨y, hy⟩ := j
    rcases x with p | q <;> rcases y with p' | q'
    · have hp := Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hx)
      have hp' := Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hy)
      show Gk p p' = gramL volume (Uc s ut) (Uc s ut) p p'
      exact hGk p.1 hp.1 p'.1 hp'.1 p.2 p'.2 (hXs _ hp.2) (hXs _ hp'.2)
    · rfl
    · rfl
    · rfl
  · rw [← hN σ h hh h' hh']
    exact h3 h hh h' hh' σ

end

end Formalism.FourierDecayAlt.P.PBK
end
