module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle309
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle306
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle300
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle259
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.SpanMoved

theorem natSmul_mem (I : AutInst) (T : Submodule (IntAf I.F I.E) (VA I)) (n : ℕ) {t : VA I} (ht : t ∈ T) :
    (n : I.E ⊗[I.F] Af I.F) • t ∈ T := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem ht n

def satG (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) :
    Submodule (IntAf I.F I.E) (VA I) where
  carrier := {x | ∃ N : ℕ, Nat.Coprime N g ∧ (N : I.E ⊗[I.F] Af I.F) • x ∈ T}
  zero_mem' := ⟨1, Nat.coprime_one_left g, by simp⟩
  add_mem' := by
    rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨N * M, Nat.coprime_mul_iff_left.2 ⟨hN, hM⟩, ?_⟩
    have e : ((N * M : ℕ) : I.E ⊗[I.F] Af I.F) • (x + y) =
        (M : I.E ⊗[I.F] Af I.F) • ((N : I.E ⊗[I.F] Af I.F) • x) +
          (N : I.E ⊗[I.F] Af I.F) • ((M : I.E ⊗[I.F] Af I.F) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (M : I.E ⊗[I.F] Af I.F)]
    rw [e]
    exact add_mem (natSmul_mem I T M hx) (natSmul_mem I T N hy)
  smul_mem' := by
    rintro r x ⟨N, hN, hx⟩
    refine ⟨N, hN, ?_⟩
    have e : (N : I.E ⊗[I.F] Af I.F) • (r • x) = r • ((N : I.E ⊗[I.F] Af I.F) • x) :=
      smul_comm _ _ _
    rw [e]
    exact T.smul_mem r hx

theorem mem_of_coprime_smul (I : AutInst) (g n : ℕ) (hn : Nat.Coprime n g)
    (T : Submodule (IntAf I.F I.E) (VA I)) (hT : mL I g ≤ T) {v : VA I} (hv : v ∈ I.Lf)
    (hnv : (n : I.E ⊗[I.F] Af I.F) • v ∈ T) : v ∈ T := by
  have hg : (g : ℤ) • v ∈ T := by
    have h : (g : I.E ⊗[I.F] Af I.F) • v ∈ mL I g := Submodule.subset_span ⟨v, hv, rfl⟩
    rw [Nat.cast_smul_eq_nsmul] at h
    rw [natCast_zsmul]
    exact hT h
  have hn' : (n : ℤ) • v ∈ T := by
    rw [Nat.cast_smul_eq_nsmul] at hnv
    rw [natCast_zsmul]
    exact hnv

  have key : v = Nat.gcdA n g • ((n : ℤ) • v) + Nat.gcdB n g • ((g : ℤ) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (Nat.gcdA n g), mul_comm (Nat.gcdB n g),
      ← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hn, Nat.cast_one, one_smul]
  rw [key]
  exact add_mem (zsmul_mem hn' _) (zsmul_mem hg _)

private theorem mem_satG_iff_exists_coprime_smul_mem (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) (x : VA I) :
    x ∈ satG I g T ↔ ∃ N : ℕ, Nat.Coprime N g ∧ (N : I.E ⊗[I.F] Af I.F) • x ∈ T := Iff.rfl

private theorem mem_satG_of_mem (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) {x : VA I}
    (hx : x ∈ T) : x ∈ satG I g T :=
  (mem_satG_iff_exists_coprime_smul_mem I g T x).2 ⟨1, Nat.coprime_one_left g, by rw [Nat.cast_one, one_smul]; exact hx⟩

private theorem map_mem_mL_of_preserves_Lf (I : AutInst) (g : ℕ) (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I)
    (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf) {x : VA I} (hx : x ∈ mL I g) : φ x ∈ mL I g := by
  have h : mL I g ≤ (mL I g).comap (φ.restrictScalars (IntAf I.F I.E)) := by
    conv_lhs => unfold mL
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show φ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ mL I g
    rw [φ.map_smul]
    exact Submodule.subset_span ⟨φ y, hφ y hy, rfl⟩
  exact h hx

theorem map_mem_satG (I : AutInst) (g : ℕ)
    (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I) (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf) (S S' : Set (VA I))
    (hS : ∀ s ∈ S, φ s ∈ satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g))
    {w : VA I} (hw : InMod I g S w) :
    φ w ∈ satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g) := by
  have hle : Submodule.span (IntAf I.F I.E) S ⊔ mL I g ≤
      (satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g)).comap (φ.restrictScalars (IntAf I.F I.E)) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro s hs
      exact hS s hs
    · intro x hx
      exact mem_satG_of_mem I g _ (Submodule.mem_sup_right (map_mem_mL_of_preserves_Lf I g φ hφ hx))
  exact hle hw

theorem map_inAt (I : AutInst) (g : ℕ)
    (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I) (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf)
    (T : Submodule (IntAf I.F I.E) (VA I)) (hT : mL I g ≤ T) {d : VA I} (hd : InAt I g g d) :
    φ d ∈ satG I g T := by
  obtain ⟨N, hN, hNd⟩ := hd
  refine (mem_satG_iff_exists_coprime_smul_mem I g T _).2 ⟨N, hN, ?_⟩
  rw [← φ.map_smul]
  exact hT (map_mem_mL_of_preserves_Lf I g φ hφ hNd)

theorem span_moved : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ v ∈ X.B.I.Lf, p v = v → InMod X.B.I X.B.g (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪ Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) v := by
  intro D X u c p hc hpL hef hzR v hv hpv
  have hcg : Nat.Coprime c X.B.g := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hc, Nat.gcd_one_left]
  let V := X.B.I.fmat (X.xu u)

  let ψ : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I :=
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (p ∘ₗ Matrix.mulVecLin V)
  have hψ : ∀ y, ψ y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (V *ᵥ y) := fun y => rfl
  have hVVi : ∀ y, V *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec]
    simp [V, Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv]
  have hK : ∀ y, y ∈ X.B.I.Lf ↔ V *ᵥ y ∈ X.B.I.Lf := X.xu_K u
  have hViL : ∀ y ∈ X.B.I.Lf, X.B.I.fmat (X.xu u)⁻¹ *ᵥ y ∈ X.B.I.Lf := fun y hy =>
    (hK _).2 (by rw [hVVi]; exact hy)
  have hψL : ∀ y ∈ X.B.I.Lf, ψ y ∈ X.B.I.Lf := fun y hy => by
    rw [hψ]
    exact hpL _ ((hK y).1 hy)
  let S' : Set (VA X.B.I) :=
    Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪
      Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))
  let T := Submodule.span (IntAf X.B.I.F X.B.I.E) S' ⊔ mL X.B.I X.B.g
  have hT : mL X.B.I X.B.g ≤ T := le_sup_right

  have hS : ∀ s ∈ Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd,
      ψ s ∈ satG X.B.I X.B.g T := by
    rintro s ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hs) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    ·
      have hfix : V *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := (X.xu_fix u a).1
      have h0 : ψ (incl X.B.I (X.eR a)) = 0 := by rw [hψ, hfix, (hef a).1, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.e0 a - incl X.B.I (X.eR a)) := (X.basisApprox a).1
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rwa [map_sub, h0, sub_zero] at h
    ·
      have hfix : V *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
      have h0 : ψ (incl X.B.I (X.fR a)) = 0 := by rw [hψ, hfix, (hef a).2, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.f0 a - incl X.B.I (X.fR a)) := (X.basisApprox a).2
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rwa [map_sub, h0, sub_zero] at h
    ·
      rw [Set.mem_singleton_iff] at hs
      subst hs
      have h0 : ψ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = 0 := by
        rw [hψ, hVVi, hzR, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) :=
        X.xu_z u
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rw [map_sub, h0, zero_sub] at h
      simpa using neg_mem h
    · exact mem_satG_of_mem X.B.I X.B.g T
        (Submodule.mem_sup_left (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
    · exact mem_satG_of_mem X.B.I X.B.g T
        (Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))

  have hmap := map_mem_satG X.B.I X.B.g ψ hψL _ S' hS (X.latticeSpan _ (hViL v hv))
  obtain ⟨N, hN, hNv⟩ := (mem_satG_iff_exists_coprime_smul_mem _ _ _ _).1 hmap
  rw [hψ, hVVi, hpv, smul_smul, ← Nat.cast_mul] at hNv
  exact mem_of_coprime_smul X.B.I X.B.g (N * c) (Nat.Coprime.mul_left hN hcg) T hT hv hNv

end GlobalTheory.St.G.SpanMoved
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset

namespace GlobalTheory.CritLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem sizes_low {D : D7} (L : SizeData₂ D) (h : SizesAt L) : L.sc.x ≤ D.R.k ∧ Real.sqrt L.sc.b ≤ L.sc.b' := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, -⟩ := h
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  refine ⟨le_trans ?_ hK.1, le_trans hW ?_⟩
  · refine Real.self_le_rpow_of_one_le hx.le ?_
    unfold szTh
    linarith
  · have hn : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
      exact_mod_cast this
    refine div_le_self ?_ (one_le_mul_of_one_le_of_one_le hx.le hn)
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity

theorem err_le (D : D7) {δ : ℝ} (hδ : 0 < δ) (h : 8 / Real.log (1 + δ) ≤ D.R.k) :
    Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1 ≤ δ := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hl : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.f ≤ D.R.k from D.R.f_le_k)
  have h2 : (D.R.k : ℝ) ^ 2 ≤ 2 ^ D.R.k := by exact_mod_cast sq_le_two_pow D.R.k (by omega)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num
  rw [sub_le_iff_le_add', ← Real.le_log_iff_exp_le (by linarith), e2]
  rw [div_le_iff₀ hl] at h
  calc (D.R.f : ℝ) * (8 / 2 ^ D.R.k) ≤ D.R.k * (8 / (D.R.k : ℝ) ^ 2) := by gcongr
    _ = 8 / D.R.k := by field_simp
    _ ≤ _ := by rw [div_le_iff₀ (by linarith)]; linarith

theorem form_of_ranks (D : D7) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (u : D.what₂.Word) (h3 : UnitaryVolumeMass.stLem3L0 D u) {C0 : ℝ}
    (hD : StandingNumericalData D C0) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := hD
  have hp := (D.mem u).A.T_prime
  have h3T : 3 ≤ (D.mem u).A.T := by
    have h1 := (hT u).2
    have h2 : 2 * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le
    have h4 : D.host.g 0 * D.host.g 1 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h5 := hp.two_le
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have h1 := (hR _ _ _ hst.1).1 hst.2.1 u
  have h2 := (h3 hp h3T (hT u).1 F0 he hz what₂ hrows).1
  have h4 : dimPi (hc := D.hcW) u = ∏ τ, vand (uS D u τ) / ∏ i ∈ range D.R.k, (i.factorial : ℝ) :=
    prod_congr rfl fun τ _ => (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D u τ)).2
  rw [h1, h2, h4]
  change _ * (Cnt.massU D.host.E D.R.k * (Tr D u ^ D.R.k - 1) ^ D.R.f) * _ =
    Cnt.massU D.host.E D.R.k * _ * _ * _
  ring

theorem along_family_of_massRatio (hM : ∀ D : D7, UnitaryVolumeMass.stMassRatio D) :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.FormalDegreeCompactDual → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) := by
  intro hE hF eps Fm Cg cb Cu cT CT C0 A hCl hR h3
  have hform : OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨x0, h⟩ := hR
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i hH u => ?_⟩
    have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
    exact form_of_ranks _ (h x ((le_max_left _ _).trans hx) i ⟨hH.2.1, hH.1, hH.2.2⟩) u (h3 x hx1 i u) hH.2.1
  refine ⟨fun x i => ?_, ?_, ?_, hform.mono fun _ _ _ _ h u u' hH => h hH.1 u, ⟨0, fun x _ i _ w τ => ?_⟩, hform⟩
  · intro τ w H _ _ z π hπ
    obtain ⟨g, -, hg⟩ := hπ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).1 H _ hg
  · refine AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 ?_ fun δ hδ => ?_
    · obtain ⟨x0, h0⟩ := hR
      refine ⟨x0, fun x hx i hH => ?_⟩
      have h := h0 x hx i
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg0, -, hg1, -, -, -, -, hv, -⟩ := hH.2.1
      have hk : (5 : ℝ) ≤ (Fm.D x i).R.k := by
        have := (Fm.D x i).R.m_add_three_le_k
        have := (Fm.D x i).R.two_le_m
        exact_mod_cast (by omega : 5 ≤ (Fm.D x i).R.k)
      have hb : 1 ≤ (Fm.L x i).sc.b :=
        Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans (Fm.L x i).sc.one_lt_alt.le) _)
      have h1 : (4 : ℝ) ≤ (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 :=
        le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
      exact ratio_ranks _ (hM _) (h hH) (lt_of_lt_of_le one_pos hv) (by exact_mod_cast h1.trans hg0)
        (by exact_mod_cast h1.trans hg1)
    · refine ⟨max (8 / Real.log (1 + δ)) (Fm.x1 + 1), fun x hx i _ => ?_⟩
      have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
      have h1 := (sizes_low _ (Fm.sizes x hx1 i)).1
      rw [Fm.L_x x i hx1] at h1
      exact err_le _ hδ (((le_max_left _ _).trans hx).trans h1)
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h1 := sizes_low _ (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i)
    exact tcrit_low _ _ _ _ _ _ _ _ _ _ hCl (vv_eq hE hF _ (Fm.ties x i)) h1.2 h1.1
  · exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).2

theorem along_family :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.FormalDegreeCompactDual → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :=
  along_family_of_massRatio GlobalTheory.T.mass_ratio_statement

end GlobalTheory.CritLevel
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset

namespace GlobalTheory.CritLevelGap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CritLevel

theorem sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem sizes_low {D : D7} (L : SizeData₂ D) (h : SizesAt L) : L.sc.x ≤ D.R.k ∧ Real.sqrt L.sc.b ≤ L.sc.b' := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, -⟩ := h
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  refine ⟨le_trans ?_ hK.1, le_trans hW ?_⟩
  · refine Real.self_le_rpow_of_one_le hx.le ?_
    unfold szTh
    linarith
  · have hn : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
      exact_mod_cast this
    refine div_le_self ?_ (one_le_mul_of_one_le_of_one_le hx.le hn)
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity

theorem err_le (D : D7) {δ : ℝ} (hδ : 0 < δ) (h : 8 / Real.log (1 + δ) ≤ D.R.k) :
    Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1 ≤ δ := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hl : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.f ≤ D.R.k from D.R.f_le_k)
  have h2 : (D.R.k : ℝ) ^ 2 ≤ 2 ^ D.R.k := by exact_mod_cast sq_le_two_pow D.R.k (by omega)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num
  rw [sub_le_iff_le_add', ← Real.le_log_iff_exp_le (by linarith), e2]
  rw [div_le_iff₀ hl] at h
  calc (D.R.f : ℝ) * (8 / 2 ^ D.R.k) ≤ D.R.k * (8 / (D.R.k : ℝ) ^ 2) := by gcongr
    _ = 8 / D.R.k := by field_simp
    _ ≤ _ := by rw [div_le_iff₀ (by linarith)]; linarith

theorem form_of_ranks (D : D7) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (u : D.what₂.Word) (h3 : UnitaryVolumeMass.stLem3L0 D u) {C0 : ℝ}
    (hD : StandingNumericalData D C0) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := hD
  have hp := (D.mem u).A.T_prime
  have h3T : 3 ≤ (D.mem u).A.T := by
    have h1 := (hT u).2
    have h2 : 2 * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le
    have h4 : D.host.g 0 * D.host.g 1 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h5 := hp.two_le
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have h1 := (hR _ _ _ hst.1).1 hst.2.1 u
  have h2 := (h3 hp h3T (hT u).1 F0 he hz what₂ hrows).1
  have h4 : dimPi (hc := D.hcW) u = ∏ τ, vand (uS D u τ) / ∏ i ∈ range D.R.k, (i.factorial : ℝ) :=
    prod_congr rfl fun τ _ => (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D u τ)).2
  rw [h1, h2, h4]
  change _ * (Cnt.massU D.host.E D.R.k * (Tr D u ^ D.R.k - 1) ^ D.R.f) * _ =
    Cnt.massU D.host.E D.R.k * _ * _ * _
  ring

theorem tcrit_low_of_dsig (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 40 ≤ Cl) (hT : Ties D) (hb' : Real.sqrt large₂.sc.b ≤ large₂.sc.b')
    (hx : large₂.sc.x ≤ D.R.k) : UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hCL : 1 ≤ Cl * large₂.sc.L := by nlinarith
  have hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := fun τ =>
    Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT hH.1 hCL τ
  exact tcrit_low D large₂ C' Cl Cg cb Cu cT CT C0 hCl hVV hb' hx hH

theorem along_family :
    Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) := by
  intro hDs eps Fm Cg cb Cu cT CT C0 A hCl hR h3
  have hM : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := GlobalTheory.MassAtRecord.massRatio_at_record
  have hform : OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨x0, h⟩ := hR
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i hH u => ?_⟩
    have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
    exact form_of_ranks _ (h x ((le_max_left _ _).trans hx) i ⟨hH.2.1, hH.1, hH.2.2⟩) u (h3 x hx1 i u) hH.2.1
  refine ⟨fun x i => ?_, ?_, ?_, hform.mono fun _ _ _ _ h u u' hH => h hH.1 u, ⟨0, fun x _ i _ w τ => ?_⟩, hform⟩
  · intro τ w H _ _ z π hπ
    obtain ⟨g, -, hg⟩ := hπ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).1 H _ hg
  · refine AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 ?_ fun δ hδ => ?_
    · obtain ⟨x0, h0⟩ := hR
      refine ⟨x0, fun x hx i hH => ?_⟩
      have h := h0 x hx i
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg0, -, hg1, -, -, -, -, hv, -⟩ := hH.2.1
      have hk : (5 : ℝ) ≤ (Fm.D x i).R.k := by
        have := (Fm.D x i).R.m_add_three_le_k
        have := (Fm.D x i).R.two_le_m
        exact_mod_cast (by omega : 5 ≤ (Fm.D x i).R.k)
      have hb : 1 ≤ (Fm.L x i).sc.b :=
        Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans (Fm.L x i).sc.one_lt_alt.le) _)
      have h1 : (4 : ℝ) ≤ (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 :=
        le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
      exact ratio_ranks _ (hM _) (h hH) (lt_of_lt_of_le one_pos hv) (by exact_mod_cast h1.trans hg0)
        (by exact_mod_cast h1.trans hg1)
    · refine ⟨max (8 / Real.log (1 + δ)) (Fm.x1 + 1), fun x hx i _ => ?_⟩
      have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
      have h1 := (sizes_low _ (Fm.sizes x hx1 i)).1
      rw [Fm.L_x x i hx1] at h1
      exact err_le _ hδ (((le_max_left _ _).trans hx).trans h1)
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h1 := sizes_low _ (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i)
    exact tcrit_low_of_dsig hDs _ _ _ _ _ _ _ _ _ _ hCl (Fm.ties x i) h1.2 h1.1
  · exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).2

end GlobalTheory.CritLevelGap
end
