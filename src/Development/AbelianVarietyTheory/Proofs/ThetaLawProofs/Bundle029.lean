module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEntireGeneratorDivFrames
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicCoordSimilitudeThetaProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_transversal_zeros_of_residue_zeros_of_isAdicComplete : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (xk : KeyIn (IsLocalRing.ResidueField O)) φ w (n d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), KeyVia xk x (IsLocalRing.residue O) φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  first | exact @GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete | exact GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete | (intros; apply GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.keyInvariantFromIntersection_unique : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KaVal x n l l' al s κ → KaVal x n l l' al s κ' → κ = κ' := by
  first | exact @GlobalTheory.KaUnique.kaVal_unique | exact GlobalTheory.KaUnique.kaVal_unique | (intros; apply GlobalTheory.KaUnique.kaVal_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq.TrVal

section Lie
variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

theorem isLieComb_comp_cast (f : G ⟶ G') [IsMonHom f] {n m : ℕ} (e : m = n) {c : Fin n → R}
    {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb (fun i => c (Fin.cast e i)) (fun i => v (Fin.cast e i) ≫ f) (w ≫ f) := by
  subst e
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu, Category.assoc]
    rfl
  · exact (map_list_prod (IsMonHom.monoidHom f (epsR R)) (List.ofFn u)).trans (by rw [List.map_ofFn]; rfl)

theorem isLieBasis_cast {n m : ℕ} (e : m = n) {v : Fin n → (epsR R ⟶ G)} (h : IsLieBasis v) :
    IsLieBasis (fun i => v (Fin.cast e i)) := by
  subst e
  exact h

end Lie

theorem exists_basis_div {G : Over (Sp ℂ)} [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR ℂ ⟶ G)}
    (hv : IsLieBasis v) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    ∃ v₀ : Fin n → (epsR ℂ ⟶ G), IsLieBasis v₀ ∧ (∀ i, IsLieComb (M⁻¹ i) v (v₀ i)) ∧
      ∀ i, IsLieComb (M i) v₀ (v i) := by
  obtain ⟨ex, tan, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ G n v hv.1
  choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists
  have hb₀ : IsLieBasis v₀ := (bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)
  obtain ⟨ex₀, -, -, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ G n v₀ hb₀.1
  refine ⟨v₀, hb₀, hv₀, fun i => ?_⟩
  obtain ⟨w, hw⟩ := (ex₀ (M i)).exists
  have h1 := comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw
  have e : ∑ j, M i j • M⁻¹ j = Pi.single i 1 := by
    rw [← Matrix.vecMul_eq_sum]
    refine (congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_
    simpa using smul_one_row (1 : ℂ) i
  rw [e] at h1
  rwa [(ex _).unique (sgl i) h1]

theorem exists_half (a : ℂ) (ha : a = 0 ∨ a = 1 / 2) (n : ℤ) :
    ∃ a' : ℂ, (a' = 0 ∨ a' = 1 / 2) ∧ ∃ k : ℤ, a' = a + n / 2 + k := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n <;> rcases ha with rfl | rfl
  · exact ⟨0, .inl rfl, -k, by push_cast; ring⟩
  · exact ⟨1 / 2, .inr rfl, -k, by push_cast; ring⟩
  · exact ⟨1 / 2, .inr rfl, -k, by push_cast; ring⟩
  · exact ⟨0, .inl rfl, -k - 1, by push_cast; ring⟩

theorem normalAt_of_param (y : KeyIn ℂ) {g : ℕ} (h : y.P.g = g) (u : HolUnif y.P.A y.P.L g)
    {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {c : ℂ} (h₁ : τ.IsSymm) (h₂ : (τ.map Complex.im).PosDef)
    (h₃ : ∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))
    (h₄ : u.IsRig y.rig) (h₅ : u.IsFn y.th (fun z => c * thetaChar τ a b z))
    (h₆ : ∀ i : Fin g, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (y.v (i.cast h.symm))) :
    NormalAt y (τ.submatrix (Fin.cast h) (Fin.cast h)) 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) c := by
  subst h
  exact ⟨u, h₁, h₂, h₃, h₄, h₅, fun i => by rw [smul_one_row]; exact h₆ i⟩

end TrVal
open TrVal

theorem val_of_isTrl : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (p : 𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) (ν : ℂˣ) (t : ℂ), IsTrl x' x p ν → Val x t → Val x' (t * (ν : ℂ) ^ 2) := by
  rintro hL hU x x' p ν t ⟨φ, hg, w, mu, rp, hp, hφ, hw, hmu, hrp, hvv, hth, r₁, r₂, r₃⟩
    ⟨τ, M, a, b, c, hab, hc, hN, rfl⟩
  have hM := det_ne_zero_of_normalAt hU x hN
  haveI := x.P.isAb.comm
  haveI := hφ
  obtain ⟨v₀, hb₀, hv₀, hv₁⟩ := exists_basis_div x.basis M hM
  obtain ⟨th₀, e₀, -, hle⟩ := exists_sec_div x.P.A.hom (mul_inv_cancel₀ hc) x.th
  obtain ⟨th₀', e₀', e₁', hle'⟩ := exists_sec_div x'.P.A.hom (mul_inv_cancel₀ hc) x'.th
  have hth₀ : ∀ s : Sp ℂ, ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀ :=
    fun s => (x.th_ne s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  have hth₀' : ∀ s : Sp ℂ, ∃ y : x'.P.A.left, x'.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀' :=
    fun s => (x'.th_ne s).imp fun y hy => ⟨hy.1, hle' hy.2⟩
  have hb₀' : IsLieBasis fun i : Fin x'.P.g => v₀ (i.cast hg) ≫ φ.inv :=
    Chart.isLieBasis_iso φ (by simpa using isLieBasis_cast hg hb₀)
  have hv₁' : ∀ i, IsLieComb (M.submatrix (Fin.cast hg) (Fin.cast hg) i)
      (fun i : Fin x'.P.g => v₀ (i.cast hg) ≫ φ.inv) (x'.v i) := fun i => by
    have := isLieComb_comp_cast φ.inv hg (hv₁ (i.cast hg))
    rw [← hvv, Category.assoc, φ.hom_inv_id, Category.comp_id] at this
    exact this
  have hN₀ := (normalAt_scale x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis th₀ hth₀ v₀ hb₀ c⁻¹ M⁻¹
    e₀ hv₀).2.2 τ M a b c hN
  rw [Matrix.nonsing_inv_mul M hM.isUnit, inv_mul_cancel₀ hc] at hN₀
  obtain ⟨u, hu⟩ := (normalAt_one_iff _ _ _ _).1 hN₀
  obtain ⟨z, rfl⟩ := u.ex_onto p
  obtain ⟨m, n, hz⟩ := (hu.2.2.1 (z + z)).1 ((u.ker _).1 (by rw [u.ex_add, ← sq]; exact hp))
  have hz' : z = frac τ 2 m n := by
    rw [frac, ← hz]
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    ring
  subst hz'
  choose a' ha' ka using fun i => exists_half (a i) (hab.1 i) (n i)
  choose b' hb' kb using fun i => exists_half (b i) (hab.2 i) (m i)
  obtain ⟨h', u', -, c', -, -, hc', hΛ, q₄, q₅, q₆⟩ := GlobalTheory.T.thetaNormalForm_translate_halfPeriod hL hU
    ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, v₀, hb₀⟩
    ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th₀', hth₀', _, hb₀'⟩ x.P.g rfl u τ a b a' b' m n ν hab ⟨ha', hb'⟩ hu ka kb
    ⟨φ, hg, w, mu, rp, hp, hφ, hw, hmu, hrp, fun i => by simp, fun z j k hj hk => by
      have e := hth z j k hj hk
      change gs _ z _ (th₀.f j) = _ * gs _ z _ (th₀'.f k)
      rw [e₀, e₀', gs_mul _ _ _ hj, gs_mul _ _ _ hk, gs_constFn _ _ _ _ hj, gs_constFn _ _ _ _ hk, e,
        Over.w, Category.id_comp, mul_left_comm], r₁, r₂, r₃⟩
  have hN₁ := normalAt_of_param ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th₀', hth₀', _, hb₀'⟩ hg u' hu.1 hu.2.1
    (fun z => (hΛ z).trans (hu.2.2.1 z)) q₄ q₅ q₆
  have hN₂ := (normalAt_scale x'.P x'.g_pos x'.rig x'.rig_gen th₀' hth₀' _ hb₀' x'.th x'.th_ne x'.v x'.basis c _
    e₁' hv₁').2.2 _ _ _ _ _ hN₁
  have hc0 : c' ≠ 0 := by
    rintro rfl
    simp at hc'
  refine ⟨_, _, _, _, _, ⟨fun i => ha' _, fun i => hb' _⟩, mul_ne_zero hc hc0, hN₂, ?_⟩
  have hd : (M.submatrix (Fin.cast hg) (Fin.cast hg)).det = M.det := Matrix.det_submatrix_equiv_self (finCongr hg) M
  rw [Matrix.mul_one, hd, eq_inv_of_mul_eq_one_right hc', mul_pow, div_mul_eq_div_div, div_eq_mul_inv _ (c' ^ 8)]

end GlobalTheory.KeyEq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

namespace GlobalTheory.SimilTheta

theorem ex_nsmul_eq_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (m : ℕ)
    (z : Fin g → ℂ) : u.ex ((m : ℤ) • z) = u.ex z ^ m := by
  rw [natCast_zsmul]
  induction m with
  | zero => simpa using GlobalTheory.CubeValues.ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_comp_id_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (m : ℕ)
    (z : Fin g → ℂ) : u.ex z ≫ (𝟙 A) ^ m = u.ex ((m : ℤ) • z) := by
  rw [ex_nsmul_eq_pow, MonObj.comp_pow, Category.comp_id]

theorem generator_mul_const_in_frames : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) → valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val = C * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := by
  intro g m x h u τ a b al hab hW hm hal mu hmu
  obtain ⟨T, hT, hT0, hTv⟩ := GlobalTheory.T.exists_entire_ne_zero_val_eq_mul_prod_frames x.P.A x.P.L g u x.P.isLB x.P.A.left (Fin 2)
    ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2] mu hmu (Fin g → ℂ) (fun z => (u.ex z).left)
    ![fun z => (m : ℤ) • z, fun z => z] u.hol
    (Fin.forall_fin_two.2 ⟨differentiable_id.const_smul (m : ℤ), differentiable_id⟩)
    (fun e => Fin.forall_fin_two.2 ⟨congrArg (fun q => q.left) (ex_comp_id_pow u m e), Category.comp_id _⟩)
  have hv : ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) →
      valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val =
        T z * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := fun z j h0 h1 => by
    refine (hTv z j (Fin.forall_fin_two.2 ⟨h0, h1⟩)).trans ?_
    rw [Fin.prod_univ_two]
    exact congrArg (fun t => T z * (t * u.fr (j 1) z ^ (-(m : ℤ) ^ 2))) (zpow_one _)
  have hper : ∀ z, ∀ l ∈ (u.Λ : Set (Fin g → ℂ)), T (z + l) = T z := by
    intro z l hl
    obtain ⟨k, n, hkn⟩ := (hW.2.2.1 l).1 hl
    obtain rfl : l = lat τ k n := hkn
    obtain ⟨i0, h0⟩ := GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex ((m : ℤ) • z)).left
    obtain ⟨i1, h1⟩ := GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex z).left
    have e1 : u.ex (z + lat τ k n) = u.ex z := GlobalTheory.CubeValues.ex_add_period u z _ hl
    have e0 : u.ex ((m : ℤ) • (z + lat τ k n)) = u.ex ((m : ℤ) • z) := by
      rw [ex_nsmul_eq_pow, e1, ex_nsmul_eq_pow]
    have A1 := hv z ![i0, i1] h0 h1
    have A2 := hv (z + lat τ k n) ![i0, i1] (by rw [e0]; exact h0) (by rw [e1]; exact h1)
    rw [e1, A1] at A2
    have n0 := u.fr_ne i0 ((m : ℤ) • (z + lat τ k n)) (by rw [e0]; exact h0)
    have n1 := u.fr_ne i1 (z + lat τ k n) (by rw [e1]; exact h1)
    have f0 := GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW ((m : ℤ) • k) ((m : ℤ) • n) i0 _ h0
    have f1 := GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW k n i1 _ h1
    rw [lat_zsmul, ← smul_add, (GlobalTheory.SimilTheta.aut_similitude_and_mul g m τ a b al hab hW.1 hm hal).2] at f0
    change T z * (u.fr i0 _ * u.fr i1 _ ^ _) = T _ * (u.fr i0 _ * u.fr i1 _ ^ _) at A2
    rw [f0, f1] at A2
    have na := aut_ne_zero τ a b k n z
    have hp : (-(m : ℤ) ^ 2) = -((m ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hp, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow] at A2
    field_simp at A2
    exact A2.symm
  refine ⟨T 0, hT0 0, fun z j h0 h1 => ?_⟩
  rw [hv z j h0 h1, GlobalTheory.entire_apply_eq_of_periodic_of_span_real hT u.full hper z 0]

end GlobalTheory.SimilTheta
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta

theorem span_single_block_eq_top {V : Type} [AddCommGroup V] [Module ℝ V] {Λ : Set V} (h : Submodule.span ℝ Λ = ⊤) :
    Submodule.span ℝ {s : Fin 4 → V | ∃ c, ∃ l ∈ Λ, s = Pi.single c l} = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hz : y c ∈ Submodule.span ℝ Λ := h ▸ Submodule.mem_top
  generalize y c = v at hz
  induction hz using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span ⟨c, v, hv, rfl⟩
  | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
  | add v v' _ _ hv hv' => rw [Pi.single_add]; exact Submodule.add_mem _ hv hv'
  | smul r v _ hv => rw [Pi.single_smul]; exact Submodule.smul_mem _ r hv

theorem ex_zsmul_eq_zpow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (s : ℤ) (z : Fin g → ℂ) :
    u.ex (s • z) = u.ex z ^ s :=
  map_zpow (MonoidHom.mk' (fun z : Multiplicative (Fin g → ℂ) => u.ex z.toAdd) fun _ _ => u.ex_add _ _)
    (Multiplicative.ofAdd z) s

theorem comp_alMap_ex {g : ℕ} (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (al : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin 4)
    (t : Fin g → ℂ) (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4)
    (hpt : ∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) :
    pt ≫ alMap x al r (u.ex t) = u.ex (∑ c, al r c • y c + t) := by
  have e₀ : pt ≫ toUnit _ = 𝟙 _ := toUnit_unique _ _
  simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
    GrpObj.comp_zpow, MonObj.comp_one, hpt, reassoc_of% e₀, Fin.sum_univ_succ, Fin.sum_univ_zero, u.ex_add, ex_zsmul_eq_zpow,
    GlobalTheory.PowUnif.ex_zero]

theorem simil_generator_eq_exp : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ (k n : Fin 4 → Fin g → ℤ) (ξ : Fin 4 → Pt x), (∀ r, ξ r = u.ex (tors τ al m k n r)) → ∀ w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4), (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → ∀ j : Fin 4 ⊕ Fin 4 → x.P.L.ι, (∀ r, ⊤ ≤ (u.ex (∑ c, al r c • y c + tors τ al m k n r)).left ⁻¹ᵁ x.P.L.U (j (Sum.inl r))) → (∀ c, ⊤ ≤ (u.ex (y c)).left ⁻¹ᵁ x.P.L.U (j (Sum.inr c))) → valAt' pt.left (LB.wchart x.P.L (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) j) (w.s j).val * Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c) = C * ((∏ r, u.fr (j (Sum.inl r)) (∑ c, al r c • y c + tors τ al m k n r)) * ∏ c, u.fr (j (Sum.inr c)) (y c) ^ (-(m : ℤ))) := by
  intro g m x h u τ a b al hab hW hm hal k n ξ hξ w hw
  obtain rfl : ξ = fun r => u.ex (tors τ al m k n r) := funext hξ
  let P : (Fin 4 → Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4) := fun y =>
    (Out.powIsLimit x.P.A 4).lift (Fan.mk _ fun c => u.ex (y c))
  have hP : ∀ y c, P y ≫ Out.powPr x.P.A c = u.ex (y c) := fun y c =>
    (Out.powIsLimit x.P.A 4).fac (Fan.mk _ fun c => u.ex (y c)) ⟨c⟩
  have hPu : ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4),
      (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → pt = P y := fun y pt hpt =>
    (Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => (hpt c).trans (hP y c).symm
  have hd : GlobalTheory.PowUnif.IsHolFamily (fun z => (u.ex z).left) := u.hol
  let z : Fin 4 ⊕ Fin 4 → (Fin 4 → Fin g → ℂ) → Fin g → ℂ :=
    Sum.elim (fun r y => ∑ c, al r c • y c + tors τ al m k n r) (fun c y => y c)
  obtain ⟨T, hT, hT0, hTv⟩ := GlobalTheory.T.exists_entire_ne_zero_val_eq_mul_prod_frames x.P.A x.P.L g u x.P.isLB _ _ _ _ w hw (Fin 4 → Fin g → ℂ)
    (fun y => (P y).left) z
    (GlobalTheory.PowUnif.isHolFamily_powObj _ 4 P fun c => by
      simp only [hP]
      exact hd.precomp (T := fun y : Fin 4 → Fin g → ℂ => y c) (by fun_prop))
    (by
      rintro (r | c)
      · change Differentiable ℂ fun y : Fin 4 → Fin g → ℂ => ∑ c, al r c • y c + tors τ al m k n r
        fun_prop
      · change Differentiable ℂ fun y : Fin 4 → Fin g → ℂ => y c
        fun_prop)
    (by
      rintro y (r | c)
      · exact congrArg (·.left) (comp_alMap_ex x u al r _ y (P y) (hP y))
      · exact congrArg (·.left) (hP y c))
  let ee : (Fin 4 → Fin g → ℂ) → ℂ := fun y =>
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)
  have hee : Differentiable ℂ ee := by
    simp only [ee, dotProduct]
    fun_prop
  have hper : ∀ y, ∀ s ∈ {s : Fin 4 → Fin g → ℂ | ∃ c, ∃ l ∈ (u.Λ : Set (Fin g → ℂ)), s = Pi.single c l},
      T (y + s) * ee (y + s) = T y * ee y := by
    rintro y _ ⟨c, l, hl, rfl⟩
    obtain ⟨k₀, n₀, hl'⟩ := (hW.2.2.1 l).1 hl
    obtain rfl : l = lat τ k₀ n₀ := hl'
    have hlat : ∀ (k n : Fin g → ℤ) (v : Fin g → ℂ), u.ex (v + lat τ k n) = u.ex v := fun k n v => by
      rw [u.ex_add, (u.ker (lat τ k n)).2 ((hW.2.2.1 _).2 ⟨k, n, rfl⟩), _root_.mul_one]
    set y' := y + Pi.single c (lat τ k₀ n₀) with hy'
    have hz₁ : ∀ r, z (Sum.inl r) y' = z (Sum.inl r) y + lat τ (al r c • k₀) (al r c • n₀) := fun r => by
      simp only [z, Sum.elim_inl, hy', Pi.add_apply, smul_add, Finset.sum_add_distrib, lat_zsmul]
      rw [Finset.sum_eq_single c (f := fun c' => al r c' • (Pi.single c (lat τ k₀ n₀) : Fin 4 → Fin g → ℂ) c')
        (fun c' _ hc => by rw [Pi.single_eq_of_ne hc, smul_zero]) (by simp),
        Pi.single_eq_same]
      abel
    have hz₂ : y' c = y c + lat τ k₀ n₀ := by simp [hy']
    have hz₃ : ∀ c', c' ≠ c → y' c' = y c' := fun c' hc => by simp [hy', Pi.single_eq_of_ne hc]
    have hex : ∀ q, u.ex (z q y') = u.ex (z q y) := by
      rintro (r | c')
      · rw [hz₁, hlat]
      · change u.ex (y' c') = u.ex (y c')
        by_cases hc : c' = c
        · rw [hc, hz₂, hlat]
        · rw [hz₃ c' hc]
    have hPP : P y' = P y := hPu y _ fun c' => (hP y' c').trans (hex (Sum.inr c'))
    choose j hj using fun q => GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex (z q y)).left
    have hj' : ∀ q, ⊤ ≤ (u.ex (z q y')).left ⁻¹ᵁ x.P.L.U (j q) := fun q => by rw [hex]; exact hj q
    have e₁ := hTv y j hj
    have e₂ := hTv y' j hj'
    rw [hPP, e₁] at e₂
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one] at e₂
    have f₁ : ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y) =
        (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
          ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y') := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hz₁]
      exact GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW _ _ _ _ (hj _)
    have f₂ : ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y) ^ (-(m : ℤ)) =
        aut τ a b k₀ n₀ (y c) ^ (-(m : ℤ)) * ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y') ^ (-(m : ℤ)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
        ← _root_.mul_assoc, ← mul_zpow]
      refine congrArg₂ (· * ·) (congrArg (· ^ _) ?_) (Finset.prod_congr rfl fun c' hc => ?_)
      · change u.fr _ (y c) = _ * u.fr _ (y' c)
        rw [hz₂]
        exact GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW _ _ _ _ (hj (Sum.inr c))
      · change u.fr _ (y c') ^ _ = u.fr _ (y' c') ^ _
        rw [hz₃ c' (Finset.ne_of_mem_erase hc)]
    have n₁ : ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y') ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun r _ => u.fr_ne _ _ (hj' _)
    have n₂ : ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y') ^ (-(m : ℤ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (u.fr_ne _ _ (hj' _))
    have e₃ : T y' = T y * (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
        aut τ a b k₀ n₀ (y c) ^ (-(m : ℤ)) := by
      rw [f₁, f₂] at e₂
      refine mul_right_cancel₀ (mul_ne_zero n₁ n₂) (e₂.symm.trans ?_)
      ring
    have e₄ : ee y' = ee y * Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ lat τ k₀ n₀)) := by
      simp only [ee, hy', Pi.add_apply, dotProduct_add, Finset.sum_add_distrib, mul_add, Complex.exp_add]
      rw [Finset.sum_eq_single c (f := fun c' => (fun i => (n c' i : ℂ)) ⬝ᵥ
          (Pi.single c (lat τ k₀ n₀) : Fin 4 → Fin g → ℂ) c')
        (fun c' _ hc => by rw [Pi.single_eq_of_ne hc, dotProduct_zero]) (by simp), Pi.single_eq_same]
    have e₅ : (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) * _ = _ :=
      (aut_similitude_and_mul g m τ a b al hab hW.1 hm hal).1 k n y c k₀ n₀
    have n₃ := pow_ne_zero m (aut_ne_zero τ a b k₀ n₀ (y c))
    rw [e₃, e₄, zpow_neg, zpow_natCast]
    calc _ = T y * ee y * ((∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
          Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ lat τ k₀ n₀))) *
          (aut τ a b k₀ n₀ (y c) ^ m)⁻¹ := by ring
      _ = _ := by rw [e₅, mul_inv_cancel_right₀ n₃]
  have hc := GlobalTheory.entire_apply_eq_of_periodic_of_span_real (F := fun y => T y * ee y) (hT.mul hee)
    (span_single_block_eq_top u.full) hper
  refine ⟨T 0 * ee 0, mul_ne_zero (hT0 0) (Complex.exp_ne_zero _), fun y pt hpt j hj₁ hj₂ => ?_⟩
  obtain rfl := hPu y pt hpt
  have e₁ := hTv y j (by rintro (r | c); exacts [hj₁ r, hj₂ c])
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one, z] at e₁
  rw [← hc y 0]
  refine (congrArg (· * ee y) e₁).trans ?_
  ring

end GlobalTheory.SimilTheta
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta


theorem _root_.GlobalTheory.T.exists_holomorphic_coord_similitudeThetaProduct : ∀ (g m : ℕ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (Th : Fin (m ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ), charHalf g a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → LevBasis a b m Th → ∀ k n : Fin 4 → Fin g → ℤ, ∃ qa : (Fin g → Fin g → ℂ) → (Fin 4 → Fin (m ^ g)) → ℂ, (∀ I, DifferentiableOn ℂ (fun p => qa p I) (Key.phDom g)) ∧ ∀ p ∈ Key.phDom g, ∀ q : (Fin 4 → Fin (m ^ g)) → ℂ, (∀ y, simTheta (per p) a b al m k n y = ∑ I, q I * ∏ c, Th (I c) p (y c)) ↔ q = qa p := by
  first | exact @GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta | exact GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta | (intros; apply GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta <;> assumption)
end
